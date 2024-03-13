include("lib/lib.jl")

using Plots
using Random

ENV["GKSwstype"] = "100" # prevent plots from displaying

abstract type Benchmark end
abstract type GenerationParams{T} end
abstract type LossParams{T} end
abstract type SimpleLossParams{T} <: LossParams{T} end
abstract type LossMgr end

abstract type Generation{T} end

struct BenchmarkMgr
    emit_stats::Function # tag::String -> ()
    # train!::Function # epochs::Integer -> learning_rate::Real -> learning_curve::Vector{<:Real}
    loss_mgr
end

function create_benchmark_manager(
    rs::RunState,
    generation_params::GenerationParams{T},
    loss_params::LossParams{T}
) where T
    println_flush(rs.io, "Building generation computation graph...")
    time_build_generation = @elapsed generation = generate(rs, generation_params)
    println_flush(rs.io, "  $(time_build_generation) seconds")
    println_flush(rs.io)

    loss_mgr = create_loss_manager(rs, loss_params, generation)

    function f_emit_stats(s::String)
        println_flush(rs.io, "Parameter values ($(s)):")
        showln(rs.io, rs.var_vals)

        generation_emit_stats(rs, generation, s)
        emit_stats(loss_mgr, s)
        generation_params_emit_stats(rs, generation_params, s)
    end

    BenchmarkMgr(f_emit_stats, loss_mgr)
end

function generation_params_emit_stats(rs::RunState, generation_params, s)
    println_flush(rs.io, "Default generation_params_emit_stats")
    println_flush(rs.io)
end

struct LossMgrImpl <: LossMgr
    emit_stats::Function # tag::String -> ()
    train!::Function # epochs::Integer -> learning_rate::Real -> learning_curve::Vector{<:Real}
end
emit_stats(m::LossMgrImpl, tag) = m.emit_stats(tag)
train!(m::LossMgrImpl; epochs, learning_rate) = m.train!(; epochs, learning_rate)


struct SimpleLossMgr <: LossMgr
    emit_stats::Function # tag::String -> ()
    train!::Function # epochs::Integer -> learning_rate::Real -> learning_curve::Vector{<:Real}
    loss::ADNode
end
emit_stats(m::SimpleLossMgr, tag) = m.emit_stats(tag)
train!(m::SimpleLossMgr; epochs, learning_rate) = m.train!(; epochs, learning_rate)

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

function create_simple_loss_manager(rs, loss)
    function emit_stats(tag)
        loss_val = compute_mixed(rs.var_vals, loss)
        println(rs.io, "Loss ($(tag)): $(loss_val)")
        println(rs.io)
    end
    function f_train(; epochs, learning_rate)
        println_flush(rs.io, "Training...")
        time_train = @elapsed learning_curve = Dice.train!(rs.var_vals, loss; epochs, learning_rate)
        println(rs.io, "  $(time_train) seconds")
        println(rs.io)

        save_learning_curve(rs.out_dir, learning_curve, "loss")
    end
    SimpleLossMgr(emit_stats, f_train, loss)
end

function train_via_sampling_entropy!(rs, e; epochs, learning_rate, resampling_frequency, samples_per_batch, consider, ignore, additional_loss, additional_loss_lr)
    learning_rate = learning_rate / samples_per_batch

    learning_curve = []
    additional_learning_curve = []

    time_sample = 0
    time_step = 0
    println_flush(rs.io, "Training...")
    for epochs_done in 0:resampling_frequency:epochs-1
        println_flush(rs.io, "Sampling...")
        time_sample_here = @elapsed samples = with_concrete_ad_flips(rs.var_vals, e) do
            [sample_as_dist(rs.rng, Valuation(), e) for _ in 1:samples_per_batch]
        end
        time_sample += time_sample_here
        println(rs.io, "  $(time_sample_here) seconds")

        loss = sum(
            LogPr(prob_equals(e, sample))
            for sample in samples
            if consider(sample)
        )
        for sample in samples
            @assert consider(sample) ^ ignore(sample)
        end

        epochs_this_batch = min(epochs - epochs_done, resampling_frequency)
        last_batch = epochs_done + epochs_this_batch == epochs

        println_flush(rs.io, "Stepping...")
        time_step_here = @elapsed subcurve, additional_subcurve = Dice.train!(
            rs.var_vals,
            [loss => learning_rate, additional_loss => additional_loss_lr];
            epochs=epochs_this_batch, append_last_loss=last_batch)
        time_step += time_step_here
        append!(learning_curve, subcurve)
        append!(additional_learning_curve, additional_subcurve)
        println(rs.io, "  $(time_step_here) seconds")
        if (isinf(last(learning_curve)) || isnan(last(learning_curve))
            || isinf(last(additional_learning_curve))
            || isnan(last(additional_learning_curve))
        )
            println(rs.io, "Stopping early due to Inf/NaN loss")
            break
        end

    end
    println(rs.io, "Sample time:  $(time_sample) seconds")
    println(rs.io, "Step time:    $(time_step) seconds")
    println(rs.io)

    save_learning_curve(rs.out_dir, learning_curve, "sampling_loss")
    save_learning_curve(rs.out_dir, additional_learning_curve, "additional_loss")
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

struct ApproxSTLCConstructorEntropy <: SimpleLossParams{STLC} end
to_subpath(::ApproxSTLCConstructorEntropy) = ["approx_entropy"]
function create_loss_manager(rs::RunState, p::ApproxSTLCConstructorEntropy, generation)
    println_flush(rs.io, "Building computation graph for $(p)...")
    time_build_loss = @elapsed loss = sum(
        neg_entropy(opt_ctor_to_id(ctor), values(stlc_ctor_to_id), ignore_non_support=true)
        for ctor in generation.constructors_overapproximation
    )
    println(rs.io, "  $(time_build_loss) seconds")
    println(rs.io)
    create_simple_loss_manager(rs, loss)
end

##################################
# Sampling STLC entropy loss
##################################

struct SamplingSTLCEntropy <: LossParams{STLC}
    resampling_frequency::Integer
    samples_per_batch::Integer
end
function SamplingSTLCEntropy(; resampling_frequency, samples_per_batch)
    SamplingSTLCEntropy(resampling_frequency, samples_per_batch)
end
to_subpath(p::SamplingSTLCEntropy) = ["sampling_entropy", "freq=$(p.resampling_frequency),spb=$(p.samples_per_batch)"]
function create_loss_manager(rs::RunState, p::SamplingSTLCEntropy, g::STLCGeneration)
    function train!(; epochs, learning_rate)
        train_via_sampling_entropy!(
            rs.io, rs.out_dir, rs.var_vals, g.e; epochs, learning_rate,
            resampling_frequency=p.resampling_frequency, samples_per_batch=p.samples_per_batch,
            consider=_->true,
            ignore=_->false,
            additional_loss=Dice.Constant(0),
            additional_loss_lr=0,
        )
    end
    LossMgrImpl(_ -> nothing, train!)
end

struct NullLoss{T} <: SimpleLossParams{T} end
to_subpath(::NullLoss) = ["null"]
function create_loss_manager(rs::RunState, ::NullLoss{T}, ::Generation{T}) where T
    create_simple_loss_manager(rs, Dice.Constant(0))
end

##################################
# Sampling STLC constructor entropy loss
##################################

struct SamplingSTLCConstructorEntropy <: LossParams{STLC}
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
    function train!(; epochs, learning_rate)
        train_via_sampling_entropy!(
            rs.io, random_ctor; epochs, learning_rate,
            resampling_frequency=p.resampling_frequency, samples_per_batch=p.samples_per_batch,
            consider=s->any(prob_equals(s, x)===true for x in values(stlc_ctor_to_id)),
            ignore=s->prob_equals(s, DistInt32(-1))===true,
            additional_loss=Dice.Constant(0),
            additional_loss_lr=0,
        )
    end
    LossMgrImpl(_ -> nothing, train!)
end

##################################
# Exact STLC constructor entropy loss
##################################

struct STLCConstructorEntropy <: SimpleLossParams{STLC} end
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
    create_simple_loss_manager(rs, loss)
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
# Sampling BST entropy loss
##################################

struct SamplingBSTEntropy <: LossParams{BST}
    resampling_frequency::Integer
    samples_per_batch::Integer
end
function SamplingBSTEntropy(; resampling_frequency, samples_per_batch)
    SamplingBSTEntropy(resampling_frequency, samples_per_batch)
end
to_subpath(p::SamplingBSTEntropy) = ["sampling_entropy", "freq=$(p.resampling_frequency),spb=$(p.samples_per_batch)"]
function create_loss_manager(rs::RunState, p::SamplingBSTEntropy, g::BSTGeneration)
    function train!(; epochs, learning_rate)
        train_via_sampling_entropy!(
            rs, g.t; epochs, learning_rate,
            resampling_frequency=p.resampling_frequency, samples_per_batch=p.samples_per_batch,
            consider=_->true,
            ignore=_->false,
            additional_loss=Dice.Constant(0),
            additional_loss_lr=0,
        )
    end
    LossMgrImpl(_ -> nothing, train!)
end

##################################
# Approx BST constructor entropy loss
##################################

struct ApproxBSTConstructorEntropy <: SimpleLossParams{BST} end
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

# struct SamplingBSTConstructorEntropy <: LossParams{BST}
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

struct MLELossParams{T} <: SimpleLossParams{T}
    metric::Metric{T}
    target_dist::TargetDist
    MLELossParams(; metric::Metric{T}, target_dist) where T = new{T}(metric, target_dist)
end
to_subpath(p::MLELossParams) = [name(p.metric), name(p.target_dist)]
function create_loss_manager(rs::RunState, p::MLELossParams, generation)
    println_flush(rs.io, "Building computation graph for $(p)...")
    time_build_loss = @elapsed begin
        metric = compute_metric(p.metric, generation)
        loss = metric_loss(metric, p.target_dist)
    end
    println(rs.io, "  $(time_build_loss) seconds")
    println(rs.io)

    mgr = create_simple_loss_manager(rs, loss)

    # Also save distribution of metric being trained
    function f_emit′(tag)
        println_flush(rs.io, "Saving $(tag) distribution...")
        time_infer = @elapsed metric_dist = pr_mixed(rs.var_vals)(metric)
        println(rs.io, "  $(time_infer) seconds")
        save_metric_dist(joinpath(rs.out_dir, "dist_$(name(p.metric))_$(tag).csv"), metric_dist; rs.io)
        println(rs.io)

        emit_stats(mgr, tag)
    end
    SimpleLossMgr(f_emit′, mgr.train!, mgr.loss)
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
# Mixed loss
##################################

struct MixedLossParams{T} <: SimpleLossParams{T}
    weighted_losses::Vector{<:Pair{<:SimpleLossParams{T}, <:Real}}
end
function to_subpath(p::MixedLossParams)
    [join(
        [
            "$(join(to_subpath(loss), "_"))_w$(weight)"
            for (loss, weight) in p.weighted_losses
        ],
        "_AND_"
    )]
end
function create_loss_manager(rs::RunState, p::MixedLossParams{T}, generation::Generation{T}) where T
    mixed_loss = Dice.Constant(0)
    mgrs = SimpleLossMgr[]
    for (subp, weight) in p.weighted_losses
        mgr::SimpleLossMgr = create_loss_manager(rs, subp, generation)
        push!(mgrs, mgr)
        mixed_loss += Dice.Constant(weight) * mgr.loss
    end
    mgr = create_simple_loss_manager(rs, mixed_loss)

    # also emit for submgrs
    function emit_stats(tag)
        mgr.emit_stats(tag)
        for submgr in mgrs
            submgr.emit_stats(tag)
        end
    end
    SimpleLossMgr(emit_stats, mgr.train!, mgr.loss)
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

struct SatisfyPropertyLoss{T} <: SimpleLossParams{T}
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

    mgr = create_simple_loss_manager(rs, loss)

    # Also print probability that property is met
    function f_emit′(tag)
        println_flush(rs.io, "Checking pr property met...")
        time_infer = @elapsed p_meets = pr_mixed(rs.var_vals)(meets_property)[true]
        println(rs.io, "  $(time_infer) seconds")

        println_flush(rs.io, "Pr meets property: $(p_meets)")
        println_flush(rs.io)

        emit_stats(mgr, tag)
    end
    SimpleLossMgr(f_emit′, mgr.train!, mgr.loss)
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

##################################
# Sampling RBT entropy loss
##################################

struct SamplingRBTEntropy <: LossParams{RBT}
    resampling_frequency::Integer
    samples_per_batch::Integer
    additional_loss_params::SimpleLossParams{RBT}
    additional_loss_lr::Real
end
function SamplingRBTEntropy(; resampling_frequency, samples_per_batch, additional_loss_params, additional_loss_lr)
    SamplingRBTEntropy(resampling_frequency, samples_per_batch, additional_loss_params, additional_loss_lr)
end
to_subpath(p::SamplingRBTEntropy) = [
    "sampling_entropy",
    "freq=$(p.resampling_frequency),spb=$(p.samples_per_batch)",
    "additional_loss=$(join(to_subpath(p.additional_loss_params),"-"))",
    "allr=$(p.additional_loss_lr)",
]
function create_loss_manager(rs::RunState, p::SamplingRBTEntropy, g::RBTGeneration)
    mgr::SimpleLossMgr = create_loss_manager(rs, p.additional_loss_params, g)
    function train!(; epochs, learning_rate)
        train_via_sampling_entropy!(
            rs, g.t; epochs, learning_rate,
            resampling_frequency=p.resampling_frequency, samples_per_batch=p.samples_per_batch,
            consider=_->true,
            ignore=_->false,
            additional_loss=mgr.loss,
            additional_loss_lr=p.additional_loss_lr,
        )
    end
    LossMgrImpl(tag -> emit_stats(mgr, tag), train!)
end

struct NullLoss{T} <: SimpleLossParams{T} end
to_subpath(::NullLoss) = ["null"]
function create_loss_manager(rs::RunState, ::NullLoss{T}) where T
    create_simple_loss_manager(rs, Dice.Constant(0))
end
