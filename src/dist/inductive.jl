# Distributions over inductively-defined types

export DistInductive, construct, prob_match

# TODO: support prob_equals
abstract type DistInductive{T} <: Dist{T} end

# All DistInductive subtypes must have these fields:
# constructor::DistUInt32
# arg_lists::Vector{Union{Vector,Nothing}}

# And support this function:
function param_lists end
# function param_lists(t::Type{<:DistInductive{<:Any}})::Dict{String,Vector{Type}}
    # error("param_lists not implemented for $(t)")
# end

function tobits(x::DistInductive)
    collect(
        Iterators.flatten([
            Iterators.flatten(
                tobits(y)
                for args in x.arg_lists
                if args !== nothing
                for y in args
            ),
            tobits(x.constructor)
        ])
    )
end

function frombits(x::DistInductive, world)
    constructor = frombits(x.constructor, world)
    dist_args = x.args_by_constructor[constructor]
    @assert dist_args !== nothing
    args = [frombits(arg, world) for arg in dist_args]
    (x.type.constructors[constructor][1], args)
end

function Base.ifelse(cond::Dist{Bool}, then::DistInductive, elze::DistInductive)
    @assert param_lists(typeof(then)) == param_lists(typeof(elze))
    typeof(then)(
        ifelse(cond, then.constructor, elze.constructor),
        [
            if then_args === nothing
                elze_args
            elseif elze_args === nothing
                then_args
            else
                ifelse(cond, then_args, elze_args)
            end
            for (then_args, elze_args) in zip(then.arg_lists, elze.arg_lists)
        ]
    )
end

function param_list_dict(t::Type{<:DistInductive})
    Dict(
        ctr => (i, params)
        for (i, (ctr, params)) in enumerate(param_lists(t))
    )
end

function construct(t::Type{<:DistInductive}, constructor::String, args::Vector)
    ctr_i, params = get(param_list_dict(t), constructor) do
        error("$(t) has no constructor $(constructor)")
    end

    @assert length(params) == length(args)
    for (param, arg) in zip(params, args)
        @assert arg isa param "$(t) $(constructor) ctr: expected $(param) got $(arg)"
    end

    arg_lists = Vector{Union{Vector,Nothing}}([nothing for _ in param_lists(t)])
    arg_lists[ctr_i] = args
    t(DistUInt32(ctr_i), arg_lists)
end

function prob_match(x::DistInductive, cases)
    pld = param_list_dict(typeof(x))

    branches = Set(map(first, cases))
    branches != keys(pld) && error("branches $(branches) do not match $(typeof(x))'s ctrs")

    res = nothing
    for (ctr, f) in cases
        i, params = pld[ctr]
        args = x.arg_lists[i]
        args === nothing && continue
        v = f(args...)
        if res === nothing
            res = v
        else
            res = ifelse(prob_equals(DistUInt32(i), x.constructor), v, res)
        end
    end
    res
end
