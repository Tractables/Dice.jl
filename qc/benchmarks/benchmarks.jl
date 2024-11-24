abstract type GenerationParams{T} end
include("lib/lib.jl")

using Plots
using Random

ENV["GKSwstype"] = "100" # prevent plots from displaying

abstract type LossConfig{T} end
abstract type LossMgr end

struct Generation
    value
    prog::Union{L.Program,Nothing}
    metadata::Dict{String,Any}
end

value(g::Generation) = g.value

function run_benchmark(
    rs::RunState,
    generation_params::GenerationParams{T},
    loss_config_weight_pairs::AbstractVector{<:Pair{<:LossConfig{T}, <:Real}},
    epochs::Integer,
    bound::Real,
) where T
    println_flush(rs.io, "Building generation computation graph...")
    time_build_generation = @elapsed generation = generate(rs, generation_params)
    println_flush(rs.io, "  $(time_build_generation) seconds")
    println_flush(rs.io)

    loss_configs, loss_weights = zip(loss_config_weight_pairs...)
    loss_mgrs = [
        create_loss_manager(rs, loss_config, generation)
        for loss_config in loss_configs
    ]
    curves = [[] for _ in loss_configs]
    al_curves = [[] for _ in loss_configs]

    function emit_stats(s::String)
        print_adnodes_of_interest(rs, s)

        println_flush(rs.io, "Parameter values ($(s)):")
        showln(rs.io, rs.var_vals)

        generation_params_emit_stats(rs, generation_params, s)

        for (i, (p, lr)) in enumerate(loss_config_weight_pairs)
            if p isa MLELossConfig
                println_flush(rs.io, "Saving $(s) distribution...")
                metric = p.metric(value(generation))
                time_infer = @elapsed metric_dist = pr_mixed(rs.var_vals)(metric)
                println(rs.io, "  $(time_infer) seconds")
                save_metric_dist(joinpath(rs.out_dir, "loss$(i)_dist_$(nameof(p.metric))_$(s).csv"), metric_dist; rs.io)
                println(rs.io)
            end
        end

        println(rs.io)
    end

    emit_stats("initial")

    for epoch in 1:epochs
        losses = [produce_loss(rs, m, epoch) for m in loss_mgrs]
        function update_curves(vals)
            for (i, loss) in enumerate(losses)
                push!(curves[i], vals[loss])
            end
        end

        vals, derivs = differentiate(
            rs.var_vals,
            Derivs(loss => w for (loss, w) in zip(losses, loss_weights))
        )
        update_curves(vals)

        for (i, m) in enumerate(loss_mgrs)
            if m isa SpecEntropyLossMgr
                a = ADComputer(Valuation())
                a.vals = vals
                al_val = compute(a, m.current_actual_loss)
                push!(al_curves[i], al_val)
            end
        end

        if any(isinf(vals[loss]) || isnan(vals[loss]) for loss in losses)
            break
        end

        # update vars
        for (adnode, d) in derivs
            if adnode isa Var
                rs.var_vals[adnode] = clamp(
                    rs.var_vals[adnode] - d,
                    inverse_sigmoid(bound),
                    inverse_sigmoid(1 - bound),
                )
                # println(rs.io, "$(adnode) $(-d)")
            end
        end

        # append last loss
        epoch == epochs && update_curves(compute(rs.var_vals, losses))
    end

    emit_stats("trained")

    for (loss_config, curve) in zip(loss_configs, curves)
        save_learning_curve(rs.out_dir, curve, join(to_subpath(loss_config), "_"))
    end

    for (al_curve, loss_config, m) in zip(al_curves, loss_configs, loss_mgrs)
        if m isa SpecEntropyLossMgr
            save_learning_curve(out_dir, al_curve, "actual_loss_" * join(to_subpath(loss_config), "_"))
            save_learning_curve(out_dir, m.num_meeting, "meets_invariant_" * join(to_subpath(loss_config), "_"))
        end
    end
end

function generation_params_emit_stats(rs::RunState, generation_params, s)
    println_flush(rs.io, "Default generation_params_emit_stats")
    println_flush(rs.io)
end

struct SimpleLossMgr <: LossMgr
    loss::ADNode
    val
    function SimpleLossMgr(loss::ADNode, val)
        # TODO: share an expander?
        l = Dice.LogPrExpander(WMC(BDDCompiler(Dice.bool_roots([loss]))))
        loss = Dice.expand_logprs(l, loss)
        new(loss, val)
    end
end
function produce_loss(rs::RunState, m::SimpleLossMgr, epoch::Integer)
    m.loss
end


struct SpecEntropy{T} <: LossConfig{T}
    resampling_frequency::Integer
    samples_per_batch::Integer
    property::Function
end

mutable struct SpecEntropyLossMgr <: LossMgr
    p::SpecEntropy
    generation
    consider
    num_meeting
    current_loss::Union{Nothing,ADNode}
    current_actual_loss::Union{Nothing,ADNode}
    current_samples
    SpecEntropyLossMgr(p, val, consider) = new(p, val, consider, [], nothing, nothing, nothing)
end

using Plots

function save_areaplot(path, v)
    mat = mapreduce(permutedims, vcat, v)
    torow(v) = reshape(v, 1, length(v))
    fontsize=18
    areaplot(
        mat,
        labels=torow(["$(i)" for i in 0:size(mat, 2)]),
        palette=cgrad(:thermal),
        tickfontsize=fontsize,
        legendfontsize=fontsize,
        fontfamily="Palatino Roman",
        fontsize=fontsize,
        xlabel="Epochs",
        ylabel="Probability",
        xlabelfontsize=fontsize,
        ylabelfontsize=fontsize,
        legend=:outertopright,
    )
    savefig("$(path).tikz")
    savefig("$(path).tex")
end

function mk_areaplot(path)
    open(path, "r") do f
        v = [[parse(Float64, s) for s in split(line,"\t")] for line in readlines(f)]
        save_areaplot(path, v)
    end
end

function to_dist(v)
    if v isa Bool
        v
    elseif v isa Unsigned
        DistUInt32(v)
    elseif v isa Integer
        DistInt32(v)
    elseif v isa Tuple
        ctor, args = v
        ctor([to_dist(arg) for arg in args]...)
    else
        error()
    end
end

clear_file(path) = open(path, "w") do f end
function produce_loss(rs::RunState, m::SpecEntropyLossMgr, epoch::Integer)
    if (epoch - 1) % m.p.resampling_frequency == 0
        sampler = sample_from_lang(rs, m.generation.prog)
        a = ADComputer(rs.var_vals)
        samples = [to_dist(sampler()) for _ in 1:m.p.samples_per_batch]
        # samples = with_concrete_ad_flips(rs.var_vals, m.generation.value) do
            # [sample_as_dist(rs.rng, a, m.generation.value) for _ in 1:m.p.samples_per_batch]
        # end

        l = Dice.LogPrExpander(WMC(BDDCompiler([
            prob_equals(m.generation.value,sample)
            for sample in samples
        ])))

        num_meeting = 0
        loss, actual_loss = sum(
            if m.consider(sample)
                num_meeting += 1
                lpr_eq = Dice.expand_logprs(l, LogPr(prob_equals(m.generation.value, sample)))
                [lpr_eq * compute(a, lpr_eq), lpr_eq]
            else
                [Dice.Constant(0), Dice.Constant(0)]
            end
            for sample in samples
        )
        push!(m.num_meeting, num_meeting / length(samples))

        loss = Dice.expand_logprs(l, loss) / length(samples)
        m.current_loss = loss
        m.current_actual_loss = actual_loss
        m.current_samples = samples
    end

    @assert !isnothing(m.current_loss)
    m.current_loss
end

function save_learning_curve(out_dir, learning_curve, name)
    open(joinpath(out_dir, "$(name).csv"), "w") do file
        xs = 0:length(learning_curve)-1
        for (epoch, logpr) in zip(xs, learning_curve)
            println(file, "$(epoch)\t$(logpr)")
        end
        plot(xs, learning_curve)
        savefig(joinpath(out_dir, "$(name).svg"))
    end
end

struct Flips{W} <: GenerationParams{Bools{W}} end
function to_subpath(::Flips)
    ["flips"]
end
function generate(rs::RunState, ::Flips{W}) where W
    Generation(
        DistUInt{W}([
            flip(register_weight!(rs, "f$(i)", random_value=true))
            for i in 1:W
        ],
        nothing,
        Dict(),
    ))
end

struct BoolsExactEntropy{W} <: LossConfig{Bools{W}} end
to_subpath(::BoolsExactEntropy) = ["exact_entropy"]
function create_loss_manager(rs::RunState, p::BoolsExactEntropy{W}, generation) where W
    println_flush(rs.io, "Building computation graph for $(p)...")
    time_build_loss = @elapsed loss = 
        neg_entropy(generation.v, [DistUInt{W}(i) for i in 0:2^W-1])
    println(rs.io, "  $(time_build_loss) seconds")
    println(rs.io)
    SimpleLossMgr(loss, generation.v)
end

##################################
# Bespoke STLC generator using Lang
##################################

struct LangBespokeSTLCGenerator <: GenerationParams{STLC}
    expr_size::Integer
    typ_size::Integer
end
LangBespokeSTLCGenerator(; expr_size, typ_size) =
    LangBespokeSTLCGenerator(expr_size, typ_size)
function to_subpath(p::LangBespokeSTLCGenerator)
    [
        "stlc",
        "langbespoke",
        "expr_sz=$(p.expr_size)-typ_sz=$(p.typ_size)",
    ]
end
function generate(rs::RunState, p::LangBespokeSTLCGenerator)
    prog = gen_expr_lang(p.expr_size, p.typ_size)
    res, prim_map, function_results = interp(rs, prog)
    Generation(res, prog, Dict(
        "ace_vals" => [interp(rs, gen_expr_lang(size, p.typ_size))[1] for size in 0:p.expr_size]
    ))
end

function generation_params_emit_stats(rs::RunState, p::LangBespokeSTLCGenerator, s)
    prog = gen_expr_lang(p.expr_size, p.typ_size)

    path = joinpath(rs.out_dir, "$(s)_Generator.v")
    open(path, "w") do file
        println(file, to_coq(rs, p, prog))
    end
    println_flush(rs.io, "Saved Coq generator to $(path)")
    println_flush(rs.io)
end


##################################
# Approx STLC constructor entropy loss
##################################

struct ApproxSTLCConstructorEntropy <: LossConfig{STLC} end
to_subpath(::ApproxSTLCConstructorEntropy) = ["approx_entropy"]
function create_loss_manager(rs::RunState, p::ApproxSTLCConstructorEntropy, generation)
    println_flush(rs.io, "Building computation graph for $(p)...")
    ace_vals = generation.metadata["ace_vals"]
    @assert length(ace_vals) == rs.p.expr_size + 1
    time_build_loss = @elapsed loss = sum(
        neg_entropy(opt_ctor_to_id(ctor), values(stlc_ctor_to_id), ignore_non_support=true)
        for ctor in ace_vals
    )
    println(rs.io, "  $(time_build_loss) seconds")
    println(rs.io)
    SimpleLossMgr(loss, nothing)
end


##################################
# Property loss
##################################

struct SatisfyPropertyLoss{T} <: LossConfig{T}
    property::Function
end
to_subpath(p::SatisfyPropertyLoss) = [nameof(p.property)]
function create_loss_manager(rs::RunState, p::SatisfyPropertyLoss, generation)
    println_flush(rs.io, "Building computation graph for $(p)...")
    time_build_loss = @elapsed begin
        meets_property = p.property(value(generation))
        loss = -LogPr(meets_property)
    end
    println(rs.io, "  $(time_build_loss) seconds")
    println(rs.io)

    SimpleLossMgr(loss, nothing)
end

alwaysTrue(t) = true
isRBT(t) = satisfies_bookkeeping_invariant(t) && satisfies_balance_invariant(t) && satisfies_order_invariant(t)
isBST(t) = satisfies_order_invariant(t)
function wellTyped(e::OptExpr.t)
    @assert isdeterministic(e)
    @match e [
        Some(e) -> (@match typecheck(e) [
            Some(_) -> true,
            None() -> false,
        ]),
        None() -> false,
    ]
end
function wellTyped(e::Expr.t)
    @assert isdeterministic(e)
    @match typecheck(e) [
        Some(_) -> true,
        None() -> false,
    ]
end


##################################
# Sampling STLC entropy loss
##################################

function SpecEntropy{T}(; resampling_frequency, samples_per_batch, property) where T
    SpecEntropy{T}(resampling_frequency, samples_per_batch, property)
end

to_subpath(p::SpecEntropy) = [
    "spec_entropy",
    "freq=$(p.resampling_frequency)-spb=$(p.samples_per_batch)",
    "prop=$(p.property)",
]
function create_loss_manager(::RunState, p::SpecEntropy{T}, g::Generation) where T
    function consider(sample)
        c = p.property(sample)
        @assert c isa Bool
        c
    end
    SpecEntropyLossMgr(p, g, consider)
end

##################################
# MLE loss
##################################

abstract type TargetDist end

struct MLELossConfig{T} <: LossConfig{T}
    metric::Function
    target_dist::TargetDist
end
to_subpath(p::MLELossConfig) = [string(nameof(p.metric)), name(p.target_dist)]
function create_loss_manager(rs::RunState, p::MLELossConfig, generation)
    println_flush(rs.io, "Building computation graph for $(p)...")
    time_build_loss = @elapsed begin
        metric = p.metric(value(generation))
        loss = metric_loss(metric, p.target_dist)
    end
    println(rs.io, "  $(time_build_loss) seconds")
    println(rs.io)

    SimpleLossMgr(loss, nothing)
end

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

struct Target4321 <: TargetDist end
name(::Target4321) = "target4321"
function metric_loss(metric::Dist, ::Target4321)
    mle_loss([
        BoolToMax(prob_equals(metric, DistUInt32(0)), weight=.4),
        BoolToMax(prob_equals(metric, DistUInt32(1)), weight=.3),
        BoolToMax(prob_equals(metric, DistUInt32(2)), weight=.2),
        BoolToMax(prob_equals(metric, DistUInt32(3)), weight=.1),
    ])
end