# The bridge between autodiff and cudd
export step_vars!, train_pr!, LogPr, compute_mixed
using DataStructures: Queue

mutable struct LogPr <: ADNode
    bool::Dist{Bool}
end
NodeType(::Type{LogPr}) = Leaf()
compute_leaf(::LogPr) = error("LogPr must be expanded")
backward(::LogPr, _, _) = error("LogPr must be expanded")

mutable struct LogPrExpander
    w::WMC
    cache::Dict{ADNode, ADNode}
    function LogPrExpander(w)
        new(w, Dict{ADNode, ADNode}())
    end
end



function expand_logprs(l::LogPrExpander, root::ADNode)::ADNode
    fl(x::LogPr) = expand_logprs(l, logprob(l.w, x.bool))
    fl(x::Var) = x
    fl(x::Constant) = x
    fi(x::Add, call) = Add(call(x.x), call(x.y))
    fi(x::Mul, call) = Mul(call(x.x), call(x.y))
    fi(x::Pow, call) = Pow(call(x.x), call(x.y))
    fi(x::Sin, call) = Sin(call(x.x))
    fi(x::Cos, call) = Cos(call(x.x))
    fi(x::Log, call) = Log(call(x.x))
    fi(x::NodeLogPr, call) = NodeLogPr(call(x.pr), call(x.hi), call(x.lo))
    foldup(root, fl, fi, ADNode, l.cache)
end

function bool_roots(root::ADNode)
    # TODO: have non-root removal be done in src/inference/cudd/compile.jl
    seen_adnodes = Dict{ADNode, Nothing}()
    seen_bools = Dict{AnyBool, Nothing}()
    non_roots = Set{AnyBool}()
    to_visit = Vector{ADNode}([root])
    while !isempty(to_visit)
        x = pop!(to_visit)
        foreach(x, seen_adnodes) do y
            if y isa LogPr
                foreach(y.bool, seen_bools) do bool
                    union!(non_roots, children(bool))
                    if bool isa Flip && bool.prob isa ADNode && !haskey(seen_adnodes, bool.prob)
                        push!(to_visit, bool.prob)
                    end
                end
            end
        end
    end
    setdiff(keys(seen_bools), non_roots)
end


# Find the log-probabilities and the log-probability gradient of a BDD
function add_scaled_dict!(
    x::AbstractDict{<:Any, <:Real},
    y::AbstractDict{<:Any, <:Real},
    s::Real
)
    for (k, v) in y
        x[k] += v * s
    end
end


function step_pr!(
    var_vals::Valuation,
    loss::ADNode,
    learning_rate::Real
)
    l = LogPrExpander(WMC(BDDCompiler(bool_roots(loss))))
    loss = expand_logprs(l, loss)
    vals, derivs = differentiate(var_vals, Derivs(loss => 1))

    # update vars
    for (adnode, d) in derivs
        if adnode isa Var
            var_vals[adnode] -= d * learning_rate
        end
    end

    vals[loss]
end

# Train group_to_psp to such that generate() approximates dataset's distribution
function train_pr!(
    var_vals::Valuation,
    loss::ADNode;
    epochs::Integer,
    learning_rate::Real,
)
    losses = []
    for _ in 1:epochs
        push!(losses, step_pr!(var_vals, loss, learning_rate))
    end
    push!(losses, compute_mixed(var_vals, loss))
    losses
end

function compute_mixed(
    var_vals::Valuation,
    x::ADNode
)
    l = LogPrExpander(WMC(BDDCompiler(bool_roots(x))))
    x = expand_logprs(l, x)
    compute(var_vals, [x])[x]
end
