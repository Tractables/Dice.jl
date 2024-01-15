abstract type Benchmark end
abstract type GenerationParams{T} end
abstract type LossParams{T} end

abstract type Generation{T} end

abstract type STLC <: Benchmark end

# STLC generation

struct STLCGenerationParams <: GenerationParams{STLC}
    param_vars_by_size::Bool
    size::Integer
    ty_size::Integer
    STLCGenerationParams(;param_vars_by_size, size, ty_size) = new(param_vars_by_size, size, ty_size)
end
struct STLCGeneration <: Generation{STLC}
    e::DistI{Opt{DistI{Expr}}}
    constructors_overapproximation::Vector{DistInt32}
end
function to_subpath(p::STLCGenerationParams)
    [
        "STLC",
        if p.param_vars_by_size "by_sz" else "not_by_sz" end,
        "sz=$(p.size),tysz=$(p.ty_size)",
    ]
end
function generate(p::STLCGenerationParams)
    constructors_overapproximation = []
    function add_ctor(v::DistI{Opt{DistI{Expr}}})
        push!(constructors_overapproximation, opt_ctor_to_id(v))
        v
    end
    e = gen_expr(
        DistNil(DistI{Typ}),
        gen_type(p.ty_size, p.param_vars_by_size),
        p.size,
        p.ty_size,
        p.param_vars_by_size,
        add_ctor,
    )
    STLCGeneration(e, constructors_overapproximation)
end

# Approx STLC constructor entropy loss

struct ApproxSTLCConstructorEntropy <: LossParams{STLC} end
to_subpath(p::ApproxSTLCConstructorEntropy) = ["approx_entropy"]
function build_loss(::ApproxSTLCConstructorEntropy, generation::STLCGeneration)
    function neg_entropy2(p::Dist, domain::Set{<:Dist})
        sum(domain) do x
            pe = prob_equals(p, x)
            if length(support_mixed(pe)) == 1
                Dice.Constant(0)
            else
                LogPr(pe) * exp(LogPr(pe))
            end
        end
    end
    loss = sum(
        neg_entropy2(ctor, Set([DistInt32(i) for i in 0:3]))
        for ctor in generation.constructors_overapproximation
        if begin
            sup = support_mixed(ctor)
            ct = sum(1 for i in 0:3 if i in sup)
            ct > 1
        end
    )
    loss, nothing
end

# MLE loss
abstract type Metric{T} end
abstract type TargetDist end

struct MLELossParams{T} <: LossParams{T}
    metric::Metric{T}
    target_dist::TargetDist
    MLELossParams(; metric::Metric{T}, target_dist) where T = new{T}(metric, target_dist)
end
to_subpath(p::MLELossParams) = [name(p.metric), name(p.target_dist)]
function build_loss(loss_params::MLELossParams{STLC}, generation::STLCGeneration)
    metric = compute_metric(loss_params.metric, generation)
    metric_loss(metric, loss_params.target_dist), metric
end

struct NumApps <: Metric{STLC} end
compute_metric(::NumApps, gen::STLCGeneration) = num_apps(gen.e)
name(::NumApps) = "num_apps"

struct TermSize <: Metric{STLC} end
compute_metric(::TermSize, gen::STLCGeneration) = term_size(gen.e)
name(::TermSize) = "term_size"

struct Uniform <: TargetDist end
name(::Uniform) = "uniform"
function metric_loss(metric::Dist, ::Uniform)
    mle_loss([
        BoolToMax(prob_equals(metric, DistUInt32(i)))
        for i in support_mixed(metric)
    ])
end

struct Linear <: TargetDist end
name(::Linear) = "linear"
function metric_loss(metric::Dist, ::Linear)
    mle_loss([
        BoolToMax(prob_equals(metric, DistUInt32(i)), weight=i)
        for i in support_mixed(metric)
    ])
end

#==
starter code for STLC exact entropy loss:

to_id = Dict(
    "Var" => DistUInt32(1),
    "Boolean" => DistUInt32(2),
    "App" => DistUInt32(3),
    "Abs" => DistUInt32(4),
)

# 99% \x. x      ["Var", "Abs"]
# 1%  (\x. x) y  ["Var", "Var", "Abs", "App"]

# dist(collect_constructors(e))
# Var => 0.99 * 1/2 + 0.01 * 2/4
# Abs => 0.99 * 1/2 + 0.01 * 1/4
# App => 0.01 * 1/4

function collect_constructors(e)
    match(e, [
        "Var"     => (i)        -> DistVector([to_id["Var"]]),
        "Boolean" => (b)        -> DistVector([to_id["Boolean"]]),
        "App"     => (f, x)    -> prob_append(prob_extend(collect_constructors(f), collect_constructors(x)), to_id["App"]),
        "Abs"     => (ty, e′)  -> prob_append(collect_constructors(e′), to_id["Abs"]),
    ])
end
random_term = match(e, [
    "None" => () -> DistNone(DistUInt32),
    "Some" => e -> DistSome(choice(collect_constructors(e)))
])
loss = neg_entropy(random_term, Set([DistSome(i) for i in values(to_id)]))
==#