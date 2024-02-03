abstract type Benchmark end
abstract type GenerationParams{T} end
abstract type LossParams{T} end
abstract type SimpleLossParams{T} <: LossParams{T} end
abstract type LossMgr end

abstract type Generation{T} end

struct BenchmarkMgr
    emit_stats::Function # tag::String -> ()
    train!::Function # epochs::Integer -> learning_rate::Real -> learning_curve::Vector{<:Real}
end


function create_benchmark_manager(
    io::IO, 
    out_dir::String,
    var_vals::Valuation, 
    generation_params::GenerationParams{T},
    loss_params::LossParams{T}
) where T
    println_flush(io, "Building generation computation graph...")
    time_build_generation = @elapsed generation = generate(generation_params)
    println(io, "  $(time_build_generation) seconds")
    println(io)

    loss_mgr = create_loss_manager(loss_params, io, out_dir, var_vals, generation)

    function emit_stats(s::String)
        println_flush(io, "Parameter values ($(s)):")
        showln(io, var_vals)

        generation_emit_stats(generation, io, out_dir, s, var_vals)
        loss_mgr.emit_stats(s)
    end

    BenchmarkMgr(emit_stats, loss_mgr.train!)
end

struct SimpleLossMgr <: LossMgr
    emit_stats::Function # tag::String -> ()
    train!::Function # epochs::Integer -> learning_rate::Real -> learning_curve::Vector{<:Real}
    loss::ADNode
end
emit_stats(m::SimpleLossMgr, tag) = m.emit_stats(tag)
train!(m::SimpleLossMgr; epochs, learning_rate) = m.train!(; epochs, learning_rate)

##################################
# STLC generation
##################################

abstract type STLC <: Benchmark end

struct STLCGenerationParams <: GenerationParams{STLC}
    param_vars_by_size::Bool
    size::Integer
    ty_size::Integer
    STLCGenerationParams(;param_vars_by_size, size, ty_size) = new(param_vars_by_size, size, ty_size)
end
struct STLCGeneration <: Generation{STLC}
    e::DistI{Opt{DistI{Expr}}}
    constructors_overapproximation::Vector{DistI{Opt{DistI{Expr}}}}
end
function to_subpath(p::STLCGenerationParams)
    [
        "stlc",
        if p.param_vars_by_size "by_sz" else "not_by_sz" end,
        "sz=$(p.size),tysz=$(p.ty_size)",
    ]
end
function generate(p::STLCGenerationParams)
    constructors_overapproximation = []
    function add_ctor(v::DistI{Opt{DistI{Expr}}})
        push!(constructors_overapproximation, v)
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

function generation_emit_stats(generation::STLCGeneration, io::IO, out_dir::String, s::String, var_vals::Valuation)
    println_flush(io, "Saving samples...")
    time_sample = @elapsed with_concrete_ad_flips(var_vals, generation.e) do
        save_samples(joinpath(out_dir, "terms_$(s).txt"), generation.e; io=io)
    end
    println(io, "  $(time_sample) seconds")
    println(io)
end

##################################
# Approx STLC constructor entropy loss
##################################

struct ApproxSTLCConstructorEntropy <: SimpleLossParams{STLC} end
to_subpath(::ApproxSTLCConstructorEntropy) = ["approx_entropy"]
function create_loss_manager(::ApproxSTLCConstructorEntropy, io, out_dir, var_vals, generation)
    loss = sum(
        neg_entropy(opt_ctor_to_id(ctor), values(stlc_ctor_to_id), ignore_non_support=true)
        for ctor in generation.constructors_overapproximation
    )
    create_simple_loss_manager(loss, io, out_dir, var_vals)
end

function create_simple_loss_manager(loss, io, out_dir, var_vals)
    function emit_stats(tag)
        loss_val = compute_mixed(var_vals, loss)
        println(io, "Loss ($(tag)): $(loss_val)")
        println(io)
    end
    function f_train(; epochs, learning_rate)
        println_flush(io, "Training...")
        time_train = @elapsed learning_curve = Dice.train!(var_vals, loss; epochs, learning_rate)
        println(io, "  $(time_train) seconds")
        println(io)

        open(joinpath(out_dir, "learning_curve.csv"), "w") do file
            for (epoch, logpr) in zip(0:epochs, learning_curve)
                println(file, "$(epoch)\t$(logpr)")
            end
        end
    end
    SimpleLossMgr(emit_stats, f_train, loss)
end

# struct SamplingSTLCConstructorEntropy <: LossParams{STLC} end
# to_subpath(::SamplingSTLCConstructorEntropy) = ["sampling_entropy"]
# function m

##################################
# Exact STLC constructor entropy loss
##################################

struct STLCConstructorEntropy <: SimpleLossParams{STLC} end
to_subpath(::STLCConstructorEntropy) = ["entropy"]
function create_loss_manager(::STLCConstructorEntropy, io, out_dir, var_vals, generation::STLCGeneration)
    random_term = match(generation.e, [
        "Some" => e -> DistSome(choice(collect_constructors(e))),
        "None" => () -> DistNone(DistInt32),
    ])
    loss = neg_entropy(random_term, Set([DistSome(i) for i in values(stlc_ctor_to_id)]))
    create_simple_loss_manager(loss, io, out_dir, var_vals)
end

##################################
# BST generation
##################################

abstract type BST <: Benchmark end

struct BSTGenerationParams <: GenerationParams{BST}
    size::Integer
    BSTGenerationParams(; size) = new(size)
end
struct BSTGeneration <: Generation{BST}
    t::DistI{Tree}
    constructors_overapproximation::Vector{DistI{Tree}}
end
function to_subpath(p::BSTGenerationParams)
    [
        "bst",
        "sz=$(p.size)",
    ]
end
function generate(p::BSTGenerationParams)
    constructors_overapproximation = []
    function add_ctor(v::DistI{Tree})
        push!(constructors_overapproximation, v)
        v
    end
    t = gen_tree(
        p.size,
        DistNat(0),
        DistNat(40),
        add_ctor,
    )
    BSTGeneration(t, constructors_overapproximation)
end

##################################
# Approx BST constructor entropy loss
##################################

struct ApproxBSTConstructorEntropy <: SimpleLossParams{BST} end
to_subpath(::ApproxBSTConstructorEntropy) = ["approx_entropy"]
function create_loss_manager(::ApproxBSTConstructorEntropy, io, out_dir, var_vals, generation::BSTGeneration)
    loss = sum(
        neg_entropy(ctor_to_id(ctor), values(bst_ctor_to_id), ignore_non_support=true)
        for ctor in generation.constructors_overapproximation
    )
    create_simple_loss_manager(loss, io, out_dir, var_vals)
end

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
function create_loss_manager(loss_params::MLELossParams{STLC}, io, out_dir, var_vals, generation::STLCGeneration)
    metric = compute_metric(loss_params.metric, generation)
    loss = metric_loss(metric, loss_params.target_dist)
    mgr = create_simple_loss_manager(loss, io, out_dir, var_vals)

    # Also save distribution of metric being trained
    function f_emit′(tag)
        println_flush(io, "Saving $(tag) distribution...")
        time_infer = @elapsed metric_dist = pr_mixed(var_vals)(metric)
        println(io, "  $(time_infer) seconds")
        save_metric_dist(joinpath(out_dir, "dist_$(name(loss_params.metric))_$(tag).csv"), metric_dist; io)
        println(io)

        emit_stats(mgr, tag)
    end
    SimpleLossMgr(f_emit′, mgr.train!, mgr.loss)
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
function create_loss_manager(p::MixedLossParams{T}, io, out_dir, var_vals, generation::Generation{T}) where T
    mixed_loss = Dice.Constant(0)
    mgrs = SimpleLossMgr[]
    for (subp, weight) in p.weighted_losses
        mgr::SimpleLossMgr = create_loss_manager(subp, io, out_dir, var_vals, generation)
        push!(mgrs, mgr)
        mixed_loss += Dice.Constant(weight) * mgr.loss
    end
    mgr = create_simple_loss_manager(mixed_loss, io, out_dir, var_vals)

    # also emit for submgrs
    function emit_stats(tag)
        mgr.emit_stats(tag)
        for submgr in mgrs
            submgr.emit_stats(tag)
        end
    end
    SimpleLossMgr(emit_stats, mgr.train!, mgr.loss)
end

