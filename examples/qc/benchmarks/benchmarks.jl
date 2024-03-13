include("lib/lib.jl")

using Plots
using Random

ENV["GKSwstype"] = "100" # prevent plots from displaying

abstract type Benchmark end
abstract type GenerationParams{T} end
abstract type LossConfig{T} end
abstract type LossMgr end

abstract type Generation{T} end

function run_benchmark(
    rs::RunState,
    generation_params::GenerationParams{T},
    loss_config_weight_pairs::AbstractVector{<:Pair{<:LossConfig{T}, <:Real}},
    epochs::Integer
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

    function emit_stats(s::String)
        print_adnodes_of_interest(rs, s)

        println_flush(rs.io, "Parameter values ($(s)):")
        showln(rs.io, rs.var_vals)

        generation_emit_stats(rs, generation, s)
        generation_params_emit_stats(rs, generation_params, s)
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

        if any(isinf(vals[loss]) || isnan(vals[loss]) for loss in losses)
            break
        end

        # update vars
        for (adnode, d) in derivs
            if adnode isa Var
                rs.var_vals[adnode] -= d
            end
        end

        # append last loss
        epoch == epochs && update_curves(compute(rs.var_vals, losses))
    end

    emit_stats("trained")

    for (loss_config, curve) in zip(loss_configs, curves)
        save_learning_curve(rs.out_dir, curve, join(to_subpath(loss_config), "_"))
    end
end

function generation_params_emit_stats(rs::RunState, generation_params, s)
    println_flush(rs.io, "Default generation_params_emit_stats")
    println_flush(rs.io)
end

struct SimpleLossMgr <: LossMgr
    loss::ADNode
    function SimpleLossMgr(loss::ADNode)
        # TODO: share an expander?
        l = Dice.LogPrExpander(WMC(BDDCompiler(Dice.bool_roots([loss]))))
        loss = Dice.expand_logprs(l, loss)
        new(loss)
    end
end
produce_loss(rs::RunState, m::SimpleLossMgr, epoch::Integer) = m.loss

struct SamplingEntropy{T} <: LossConfig{T}
    resampling_frequency::Integer
    samples_per_batch::Integer
end

mutable struct SamplingEntropyLossMgr <: LossMgr
    p::SamplingEntropy
    val::Dist
    consider
    ignore
    current_loss::Union{Nothing,ADNode}
    SamplingEntropyLossMgr(p, val, consider, ignore) = new(p, val, consider, ignore, nothing)
end
function produce_loss(rs::RunState, m::SamplingEntropyLossMgr, epoch::Integer)
    if (epoch - 1) % m.p.resampling_frequency == 0
        println_flush(rs.io, "Sampling...")
        time_sample = @elapsed samples = with_concrete_ad_flips(rs.var_vals, m.val) do
            [sample_as_dist(rs.rng, Valuation(), m.val) for _ in 1:m.p.samples_per_batch]
        end
        println(rs.io, "  $(time_sample) seconds")

        loss = sum(
            LogPr(prob_equals(m.val, sample))
            for sample in samples
            if m.consider(sample)
        )
        for sample in samples
            @assert m.consider(sample) ^ m.ignore(sample)
        end
        l = Dice.LogPrExpander(WMC(BDDCompiler(Dice.bool_roots([loss]))))
        loss = Dice.expand_logprs(l, loss) / m.p.samples_per_batch
        m.current_loss = loss
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

##################################
# STLC generation
##################################

abstract type STLC <: Benchmark end
struct STLCGeneration <: Generation{STLC}
    e::DistI{Opt{DistI{Expr}}}
    constructors_overapproximation::Vector{DistI{Opt{DistI{Expr}}}}
end
function generation_emit_stats(rs::RunState, g::STLCGeneration, s::String)
    println_flush(rs.io, "Saving samples...")
    time_sample = @elapsed with_concrete_ad_flips(rs.var_vals, g.e) do
        save_samples(joinpath(rs.out_dir, "terms_$(s).txt"), g.e; io=rs.io)
    end
    println(rs.io, "  $(time_sample) seconds")
    println(rs.io)
end
value(g::STLCGeneration) = g.e

##################################
# Bespoke STLC generator
##################################

struct BespokeSTLCGenerator <: GenerationParams{STLC}
    param_vars_by_size::Bool
    size::Integer
    ty_size::Integer
end
BespokeSTLCGenerator(;param_vars_by_size, size, ty_size) = BespokeSTLCGenerator(param_vars_by_size, size, ty_size)
function to_subpath(p::BespokeSTLCGenerator)
    [
        "stlc",
        "bespoke",
        if p.param_vars_by_size "by_sz" else "not_by_sz" end,
        "sz=$(p.size)-tysz=$(p.ty_size)",
    ]
end
function generate(rs::RunState, p::BespokeSTLCGenerator)
    constructors_overapproximation = []
    function add_ctor(v::DistI{Opt{DistI{Expr}}})
        push!(constructors_overapproximation, v)
        v
    end
    e = gen_expr(
        rs,
        DistNil(DistI{Typ}),
        gen_type(rs, p.ty_size, p.param_vars_by_size),
        p.size,
        p.ty_size,
        p.param_vars_by_size,
        add_ctor,
    )
    STLCGeneration(e, constructors_overapproximation)
end

function generation_params_emit_stats(rs::RunState, p::BespokeSTLCGenerator, s)
    if p == BespokeSTLCGenerator(param_vars_by_size=true,size=5,ty_size=2)
        path = joinpath(rs.out_dir, "$(s)_Generator.v")
        open(path, "w") do file
            vals = compute(rs.var_vals, values(rs.adnodes_of_interest))
            adnodes_vals = Dict(s => vals[adnode] for (s, adnode) in rs.adnodes_of_interest)
            println(file, bespoke_stlc_to_coq(adnodes_vals))
        end
        println_flush(rs.io, "Saved Coq generator to $(path)")
    else
        println_flush(rs.io, "Translation back to Coq not defined")
    end
    println_flush(rs.io)
end

##################################
# Type-based STLC generator
##################################

struct TypeBasedSTLCGenerator <: GenerationParams{STLC}
    size::Integer
    ty_size::Integer
end
TypeBasedSTLCGenerator(; size, ty_size) = TypeBasedSTLCGenerator(size, ty_size)
function to_subpath(p::TypeBasedSTLCGenerator)
    [
        "stlc",
        "typebased",
        "sz=$(p.size)-tysz=$(p.ty_size)",
    ]
end
function generate(rs::RunState, p::TypeBasedSTLCGenerator)
    constructors_overapproximation = []
    function add_ctor(v::DistI{Expr})
        push!(constructors_overapproximation, DistSome(v))
        v
    end
    e = tb_gen_expr(rs, p.size, p.ty_size, add_ctor)
    STLCGeneration(DistSome(e), constructors_overapproximation)
end

##################################
# Approx STLC constructor entropy loss
##################################

struct ApproxSTLCConstructorEntropy <: LossConfig{STLC} end
to_subpath(::ApproxSTLCConstructorEntropy) = ["approx_entropy"]
function create_loss_manager(rs::RunState, p::ApproxSTLCConstructorEntropy, generation)
    println_flush(rs.io, "Building computation graph for $(p)...")
    time_build_loss = @elapsed loss = sum(
        neg_entropy(opt_ctor_to_id(ctor), values(stlc_ctor_to_id), ignore_non_support=true)
        for ctor in generation.constructors_overapproximation
    )
    println(rs.io, "  $(time_build_loss) seconds")
    println(rs.io)
    SimpleLossMgr(loss)
end

##################################
# Sampling STLC entropy loss
##################################

function SamplingEntropy{T}(; resampling_frequency, samples_per_batch) where T
    SamplingEntropy{T}(resampling_frequency, samples_per_batch)
end
to_subpath(p::SamplingEntropy) = ["sampling_entropy", "freq=$(p.resampling_frequency),spb=$(p.samples_per_batch)"]
function create_loss_manager(::RunState, p::SamplingEntropy{T}, g::Generation{T}) where T
    SamplingEntropyLossMgr(p, value(g), _->true, _->false)
end

##################################
# Sampling STLC constructor entropy loss
##################################

struct SamplingSTLCConstructorEntropy <: LossConfig{STLC}
    resampling_frequency::Integer
    samples_per_batch::Integer
end
function SamplingSTLCConstructorEntropy(; resampling_frequency, samples_per_batch)
    SamplingSTLCConstructorEntropy(resampling_frequency, samples_per_batch)
end
to_subpath(p::SamplingSTLCConstructorEntropy) = ["sampling_ctor_entropy", "freq=$(p.resampling_frequency),spb=$(p.samples_per_batch)"]
function create_loss_manager(rs::RunState, p::SamplingSTLCConstructorEntropy, g::STLCGeneration)
    println_flush(rs.io, "Building random_ctor graph...")
    time_build_random_ctor = @elapsed random_ctor = match(g.e, [
        "Some" => e -> choice(collect_constructors(e)),
        "None" => () -> DistInt32(-1),
    ])
    println(rs.io, "  $(time_build_random_ctor) seconds")

    SamplingEntropyLossMgr(p, random_ctor,
        s->any(prob_equals(s, x)===true for x in values(stlc_ctor_to_id)),
        s->prob_equals(s, DistInt32(-1))===true)
end

##################################
# Exact STLC constructor entropy loss
##################################

struct STLCConstructorEntropy <: LossConfig{STLC} end
to_subpath(::STLCConstructorEntropy) = ["ctor_entropy"]
function create_loss_manager(rs::RunState, p::STLCConstructorEntropy, generation::STLCGeneration)
    println_flush(rs.io, "Building computation graph for $(p)...")
    time_build_loss = @elapsed begin
        random_term = match(generation.e, [
            "Some" => e -> DistSome(choice(collect_constructors(e))),
            "None" => () -> DistNone(DistInt32),
        ])
        loss = neg_entropy(random_term, Set([DistSome(i) for i in values(stlc_ctor_to_id)]))
    end
    println(rs.io, "  $(time_build_loss) seconds")
    println(rs.io)

    SimpleLossMgr(loss)
end

##################################
# BST generation
##################################

abstract type BST <: Benchmark end
struct BSTGeneration <: Generation{BST}
    t::DistI{Tree}
    constructors_overapproximation::Vector{DistI{Tree}}
end
function generation_emit_stats(rs::RunState, g::BSTGeneration, s::String)
end
value(g::BSTGeneration) = g.t

##################################
# Bespoke BST generator
##################################

@enum BSTValues BSTActualVals BSTDummyVals BSTApproxVals
function str(x::BSTValues)
    if x == BSTActualVals
        "actual"
    elseif x == BSTDummyVals
        "dummy"
    elseif x == BSTApproxVals
        "approx"
    else
        error("")
    end
end

struct BespokeBSTGenerator <: GenerationParams{BST}
    size::Integer
    vals::BSTValues
end
BespokeBSTGenerator(; size, vals) = BespokeBSTGenerator(size, vals)
function to_subpath(p::BespokeBSTGenerator)
    [
        "bst",
        "bespoke",
        str(p.vals),
        "sz=$(p.size)",
    ]
end
function generate(rs::RunState, p::BespokeBSTGenerator)
    constructors_overapproximation = []
    function add_ctor(v::DistI{Tree})
        push!(constructors_overapproximation, v)
        v
    end
    t = if p.vals == BSTDummyVals
        gen_tree_dummy_vals(rs, p.size, add_ctor)
    elseif p.vals == BSTApproxVals
        gen_tree(rs, p.size, DistNat(0), DistNat(40), true, add_ctor)
    elseif p.vals == BSTActualVals
        gen_tree(rs, p.size, DistNat(0), DistNat(40), false, add_ctor)
    else
        error()
    end

    BSTGeneration(t, constructors_overapproximation)
end

##################################
# Type-based BST generator
##################################

struct TypeBasedBSTGenerator <: GenerationParams{BST}
    size::Integer
end
TypeBasedBSTGenerator(; size) = TypeBasedBSTGenerator(size)
function to_subpath(p::TypeBasedBSTGenerator)
    [
        "bst",
        "typebased",
        "sz=$(p.size)",
    ]
end
function generate(rs::RunState, p::TypeBasedBSTGenerator)
    constructors_overapproximation = []
    function add_ctor(v::DistI{Tree})
        push!(constructors_overapproximation, v)
        v
    end
    t = typebased_gen_tree(rs, p.size, add_ctor)
    BSTGeneration(t, constructors_overapproximation)
end

##################################
# Approx BST constructor entropy loss
##################################

struct ApproxBSTConstructorEntropy <: LossConfig{BST} end
to_subpath(::ApproxBSTConstructorEntropy) = ["approx_ctor_entropy"]
function create_loss_manager(rs::RunState, p::ApproxBSTConstructorEntropy, generation::BSTGeneration)
    println_flush(rs.io, "Building computation graph for $(p)...")
    time_build_loss = @elapsed loss = sum(
        neg_entropy(ctor_to_id(ctor), values(bst_ctor_to_id), ignore_non_support=true)
        for ctor in generation.constructors_overapproximation
    )
    println(rs.io, "  $(time_build_loss) seconds")
    println(rs.io)
    create_simple_loss_manager(rs, loss)
end

##################################
# Sampling BST constructor entropy loss
##################################

# struct SamplingBSTConstructorEntropy <: LossConfig{BST}
#     resampling_frequency::Integer
#     samples_per_batch::Integer
#     function SamplingBSTConstructorEntropy(; resampling_frequency, samples_per_batch)
#         new(resampling_frequency, samples_per_batch)
#     end
# end
# to_subpath(p::SamplingBSTConstructorEntropy) = ["sampling_entropy", "freq=$(p.resampling_frequency),spb=$(p.samples_per_batch)"]
# function create_loss_manager(p::SamplingBSTConstructorEntropy, io, out_dir, var_vals, g::BSTGeneration)
#     println_flush(io, "Building random_ctor graph...")
#     time_build_random_ctor = @elapsed random_ctor = match(g.constructors_overapproximation, [
#         "Some" => e -> choice(collect_constructors(e)), # TODO: implement collect_constructors
#         "None" => () -> DistInt32(-1),
#     ])
#     println(io, "  $(time_build_random_ctor) seconds")
#     function train!(; epochs, learning_rate)
#         train_via_sampling_entropy!(
#             io, out_dir, var_vals, random_ctor; epochs, learning_rate,
#             resampling_frequency=p.resampling_frequency, samples_per_batch=p.samples_per_batch,
#             domain=values(bst_ctor_to_id),
#             ignored_domain=[DistInt32(-1)]
#         )
#     end
#     LossMgrImpl(_ -> nothing, train!)
# end

##################################
# MLE loss
##################################

abstract type Metric{T} end
abstract type TargetDist end

struct MLELossConfig{T} <: LossConfig{T}
    metric::Metric{T}
    target_dist::TargetDist
    MLELossConfig(; metric::Metric{T}, target_dist) where T = new{T}(metric, target_dist)
end
to_subpath(p::MLELossConfig) = [name(p.metric), name(p.target_dist)]
function create_loss_manager(rs::RunState, p::MLELossConfig, generation)
    println_flush(rs.io, "Building computation graph for $(p)...")
    time_build_loss = @elapsed begin
        metric = compute_metric(p.metric, generation)
        loss = metric_loss(metric, p.target_dist)
    end
    println(rs.io, "  $(time_build_loss) seconds")
    println(rs.io)

    SimpleLossMgr(loss)

    # TODO: fix. allow us to register_stats! to rs, or create MLELossMgr
    # # Also save distribution of metric being trained
    # function f_emit′(tag)
    #     println_flush(rs.io, "Saving $(tag) distribution...")
    #     time_infer = @elapsed metric_dist = pr_mixed(rs.var_vals)(metric)
    #     println(rs.io, "  $(time_infer) seconds")
    #     save_metric_dist(joinpath(rs.out_dir, "dist_$(name(p.metric))_$(tag).csv"), metric_dist; rs.io)
    #     println(rs.io)

    #     emit_stats(mgr, tag)
    # end
end

struct TreeSize <: Metric{BST} end
compute_metric(::TreeSize, gen::BSTGeneration) = tree_size(gen.t)
name(::TreeSize) = "tree_size"

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
##################################
# RBT generation
##################################

abstract type RBT <: Benchmark end
struct RBTGeneration <: Generation{RBT}
    t::DistI{RBTree}
end
function generation_emit_stats(::RunState, g::RBTGeneration, s::String)
end
value(g::RBTGeneration) = g.t

##################################
# Type-based RBT generator
##################################

struct TypeBasedRBTGenerator <: GenerationParams{RBT}
    size::Integer
    color_by_size::Bool
    learn_leaf_weights::Bool
    use_parent_color::Bool
end
TypeBasedRBTGenerator(; size, color_by_size, learn_leaf_weights, use_parent_color) =
    TypeBasedRBTGenerator(size, color_by_size, learn_leaf_weights, use_parent_color)
function to_subpath(p::TypeBasedRBTGenerator)
    [
        "rbt",
        "typebased",
        "sz=$(p.size)",
        "color_by_size=$(p.color_by_size)",
        "learn_leaf_weights=$(p.learn_leaf_weights)",
        "use_parent_color=$(p.use_parent_color)",
    ]
end
function generate(rs::RunState, p::TypeBasedRBTGenerator)
    RBTGeneration(tb_gen_rbt(rs, p, p.size, false))
end
function generation_params_emit_stats(rs::RunState, p::TypeBasedRBTGenerator, s)
    path = joinpath(rs.out_dir, "$(s)_Generator.v")
    open(path, "w") do file
        vals = compute(rs.var_vals, values(rs.adnodes_of_interest))
        adnodes_vals = Dict(s => vals[adnode] for (s, adnode) in rs.adnodes_of_interest)
        println(file, typebased_rbt_to_coq(p, adnodes_vals, rs.io))
    end
    println_flush(rs.io, "Saved Coq generator to $(path)")
end

abstract type Property{T} end

struct SatisfyPropertyLoss{T} <: LossConfig{T}
    property::Property{T}
end
to_subpath(p::SatisfyPropertyLoss) = [name(p.property)]
function create_loss_manager(rs::RunState, p::SatisfyPropertyLoss, generation)
    println_flush(rs.io, "Building computation graph for $(p)...")
    time_build_loss = @elapsed begin
        meets_property = check_property(p.property, generation)
        loss = -LogPr(meets_property)
    end
    println(rs.io, "  $(time_build_loss) seconds")
    println(rs.io)

    SimpleLossMgr(loss)

    # TODO: fix
    # # Also print probability that property is met
    # function f_emit′(tag)
    #     println_flush(rs.io, "Checking pr property met...")
    #     time_infer = @elapsed p_meets = pr_mixed(rs.var_vals)(meets_property)[true]
    #     println(rs.io, "  $(time_infer) seconds")

    #     println_flush(rs.io, "Pr meets property: $(p_meets)")
    #     println_flush(rs.io)

    #     emit_stats(mgr, tag)
    # end
end

struct BookkeepingInvariant <: Property{RBT} end
check_property(::BookkeepingInvariant, g::RBTGeneration) =
    satisfies_bookkeeping_invariant(g.t)
name(::BookkeepingInvariant) = "bookkeeping"

struct BalanceInvariant <: Property{RBT} end
check_property(::BalanceInvariant, g::RBTGeneration) =
    satisfies_balance_invariant(g.t)
name(::BalanceInvariant) = "balance"

struct BlackRootInvariant <: Property{RBT} end
check_property(::BlackRootInvariant, g::RBTGeneration) =
    satisfies_black_root_invariant(g.t)
name(::BlackRootInvariant) = "blackroot"

struct MultipleInvariants{T} <: Property{T}
    properties::Vector{<:Property{T}}
end
check_property(p::MultipleInvariants{T}, g::Generation{T}) where T = 
    reduce(&, [
        check_property(property, g)
        for property in p.properties
    ])
name(p::MultipleInvariants{T}) where T =
    join([name(property) for property in p.properties], "AND")
