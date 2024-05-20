include("lib/lib.jl")

using Plots
using Random

ENV["GKSwstype"] = "100" # prevent plots from displaying

abstract type Benchmark end
abstract type GenerationParams{T} end
abstract type LossConfig{T} end
abstract type LossMgr end

abstract type Generation{T} end

abstract type Property{T} end

function workload_of(::Type{<:GenerationParams{T}}) where T
    T
end

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
    
    generation_emit_stats(rs, generation, "test")

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

        for (i, m) in enumerate(loss_mgrs)
            if m isa SamplingEntropyLossMgr
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
                rs.var_vals[adnode] -= d
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
        if m isa SamplingEntropyLossMgr
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
    # dist_path = joinpath(rs.out_dir, "dist.csv")
    # if epoch == 1
    #     clear_file(dist_path)
    # end
    # d = pr_mixed(rs.var_vals)(m.val)
    # open(dist_path, "a") do f
    #     println(f, join([d[i] for i in 0:15],"\t"))
    # end
    # if epoch == EPOCHS
    #     mk_areaplot(dist_path)
    # end
    
    m.loss
end


struct SamplingEntropy{T} <: LossConfig{T}
    resampling_frequency::Integer
    samples_per_batch::Integer
    property::Property{T}
    eq::Symbol
    failure_penalty::Real
    forgiveness::Real
    rand_forgiveness::Bool
end

mutable struct SamplingEntropyLossMgr <: LossMgr
    p::SamplingEntropy
    val
    consider
    num_meeting
    current_loss::Union{Nothing,ADNode}
    current_actual_loss::Union{Nothing,ADNode}
    current_samples
    SamplingEntropyLossMgr(p, val, consider) = new(p, val, consider, [], nothing, nothing, nothing)
end

function save_areaplot(path, v)
    mat = mapreduce(permutedims, vcat, v)
    torow(v) = reshape(v, 1, length(v))
    areaplot(
        mat,
        labels=torow(["$(i)" for i in 0:size(mat, 2)]),
        legend=false,
        # palette=:lightrainbow)
        palette=cgrad(:thermal)
    )
    savefig("$(path).svg")
end

function mk_areaplot(path)
    open(path, "r") do f
        v = [[parse(Float64, s) for s in split(line,"\t")] for line in readlines(f)]
        save_areaplot(path, v)
    end
end

clear_file(path) = open(path, "w") do f end
function produce_loss(rs::RunState, m::SamplingEntropyLossMgr, epoch::Integer)
    if (epoch - 1) % m.p.resampling_frequency == 0
        a = ADComputer(rs.var_vals)
        samples = with_concrete_ad_flips(rs.var_vals, m.val) do
            [sample_as_dist(rs.rng, a, m.val) for _ in 1:m.p.samples_per_batch]
        end

        l = Dice.LogPrExpander(WMC(BDDCompiler([
            prob_equals(m.val,sample)
            for sample in samples
        ])))

        num_meeting = 0
        f_eq = if m.p.eq == :eq_num_apps eq_num_apps
        elseif m.p.eq == :eq_has_app eq_has_app
        elseif m.p.eq == :sat1_eq_num_apps begin (x, y) -> sat_eq_num_apps(x, y, 1) end
        elseif m.p.eq == :sat2_eq_num_apps begin (x, y) -> sat_eq_num_apps(x, y, 2) end
        elseif m.p.eq == :eq_except_numbers eq_except_numbers
        elseif m.p.eq == :eq_structure eq_structure
        elseif m.p.eq == :prob_equals prob_equals
        else error() end
        loss, actual_loss = sum(
            begin
                lpr_eq = LogPr(f_eq(m.val, sample))
                lpr_eq_expanded = Dice.expand_logprs(l, lpr_eq)
                # diff_test_typecheck(sample, Dice.frombits(sample, Dict()))
                meets = m.consider(sample)
                meets && (num_meeting += 1)

                loss_here, actual_loss_here = if meets || (m.p.rand_forgiveness && rand(rs.rng) < m.p.forgiveness)
                    (
                        lpr_eq_expanded * compute(a, lpr_eq_expanded),
                        lpr_eq_expanded
                    )
                elseif !meets && !m.p.rand_forgiveness
                    (
                        Dice.Constant(m.p.forgiveness) * lpr_eq_expanded * compute(a, lpr_eq_expanded),
                        Dice.Constant(m.p.forgiveness) * lpr_eq_expanded
                    )
                else
                    Dice.Constant(0), Dice.Constant(0)
                end

                if !meets
                    loss_here += Dice.Constant(m.p.failure_penalty)
                    actual_loss_here += Dice.Constant(m.p.failure_penalty)
                end

                [loss_here, actual_loss_here]
            end
            for sample in samples
        )
        push!(m.num_meeting, num_meeting / length(samples))

        loss = Dice.expand_logprs(l, loss) / length(samples)
        m.current_loss = loss
        m.current_actual_loss = actual_loss
        m.current_samples = samples
    end

    # samples_path = joinpath(rs.out_dir, "samples.csv")
    # dist_path = joinpath(rs.out_dir, "dist.csv")
    # if epoch == 1
    #     clear_file(samples_path)
    #     clear_file(dist_path)
    # end
    # d = pr_mixed(rs.var_vals)(m.val)
    # open(dist_path, "a") do f
    #     println(f, join([d[i] for i in 0:15],"\t"))
    # end
    # open(samples_path, "a") do f
    #     println(f, join([
    #         count(s -> prob_equals(s, DistUInt{4}(i)) === true, m.current_samples)
    #         for i in 0:15
    #     ], "\t"))
    # end
    # if epoch == EPOCHS
    #     mk_areaplot(samples_path)
    #     mk_areaplot(dist_path)
    # end

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

abstract type Bools{W} <: Benchmark end
struct BoolsGeneration{W} <: Generation{Bools{W}}
    v::DistUInt{W}
end
value(g::BoolsGeneration) = g.v
function generation_emit_stats(rs::RunState, g::BoolsGeneration, s::String)
end

struct Flips{W} <: GenerationParams{Bools{W}} end
function to_subpath(::Flips)
    ["flips"]
end
function generate(rs::RunState, ::Flips{W}) where W
    BoolsGeneration(DistUInt{W}([
        flip(register_weight!(rs, "f$(i)", random_value=true))
        for i in 1:W
    ]))
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
# LRUSetTestcase Generation
##################################
abstract type LRUSetTestcase <: Benchmark end
struct LRUSetTestcaseGeneration <: Generation{LRUSetTestcase}
    v::LRUS.Program
end
value(g::LRUSetTestcaseGeneration) = g.v
function generation_emit_stats(rs::RunState, g::LRUSetTestcaseGeneration, s::String)
    p = pr_mixed(rs.var_vals)(prob_equals(
        g.v,
        LRUS.vec_to_program([
            LRUS.Insert(DistInt32(0)),
            LRUS.Insert(DistInt32(1)),
            LRUS.Insert(DistInt32(0)),
            LRUS.PopStale(),
            LRUS.Contains(DistInt32(1)),
        ]),
    ))[true]
    # 3 p 2 * 2 c 1 = 12 ways to make programs like the above
    println(rs.io, "Pr of finding bug: $(12 * p)")
    println()
end

struct BespokeLRUSetTestcaseGenerator <: GenerationParams{LRUSetTestcase}
    size
end
function to_subpath(::BespokeLRUSetTestcaseGenerator)
    ["BespokeLRUSetTestcaseGenerator"]
end
function generate(rs::RunState, p::BespokeLRUSetTestcaseGenerator)
    LRUSetTestcaseGeneration(
        bespoke_gen_lrusp(rs, p.size)
    )
end

##################################
# STLC generation
##################################

abstract type STLC <: Benchmark end
function sandwich(::Type{STLC})
    (
        "From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.",
"Definition test_prop_SinglePreserve :=
forAll gSized (fun (e: Expr) =>
  prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)

Definition test_prop_MultiPreserve :=
forAll gSized (fun (e: Expr) =>
  prop_MultiPreserve e).

(*! QuickChick test_prop_MultiPreserve. *)
          "
    )
end


struct STLCGeneration <: Generation{STLC}
    e::Opt.T{Expr.T}
    constructors_overapproximation::Vector{Opt.T{Expr.T}}
end
function generation_emit_stats(rs::RunState, g::STLCGeneration, s::String)
    println_flush(rs.io, "Saving samples...")
    # time_sample = @elapsed with_concrete_ad_flips(rs.var_vals, g.e) do
    #     save_samples(rs, joinpath(rs.out_dir, "terms_$(s).txt"), g.e)
    # end
    # println(rs.io, "  $(time_sample) seconds")
    # println(rs.io)
end
value(g::STLCGeneration) = g.e

##################################
# DerivedGenerator
##################################

struct DerivedGenerator{T} <: GenerationParams{T}
    root_ty::Type
    ty_sizes::Vector{Pair{Type, Integer}}
    stack_size::Integer
    intwidth::Integer
end
DerivedGenerator{T}(; root_ty, ty_sizes, stack_size, intwidth) where T =
    DerivedGenerator{T}(root_ty, ty_sizes, stack_size, intwidth)
function to_subpath(p::DerivedGenerator{T}) where T
    [
        lowercase(string(T)),
        "derived",
        "root_ty=$(p.root_ty)",
        "ty-sizes=$(join(["$(ty)-$(size)" for (ty, size) in p.ty_sizes],"-"))",
        "stack_size=$(p.stack_size)",
        "intwidth=$(p.intwidth)",
    ]
end
function generate(rs::RunState, p::DerivedGenerator{T}) where T
    constructors_overapproximation = []
    function add_ctor(v::Opt.T{Expr.T})
        push!(constructors_overapproximation, v)
        v
    end
    e = generate(rs, p, add_ctor)
    if T == STLC
        STLCGeneration(Opt.Some(e), constructors_overapproximation)
    elseif T == BST
        BSTGeneration(e, constructors_overapproximation)
    elseif T == RBT
        RBTGeneration(e)
    else
        error()
    end
end
function generation_params_emit_stats(rs::RunState, p::DerivedGenerator, s)
    save_coq_generator(rs, p, s, derived_to_coq)
end

function save_coq_generator(rs, p, s, f)
    path = joinpath(rs.out_dir, "$(s)_Generator.v")
    open(path, "w") do file
        vals = compute(rs.var_vals, values(rs.adnodes_of_interest))
        adnodes_vals = Dict(s => vals[adnode] for (s, adnode) in rs.adnodes_of_interest)
        println(file, f(p, adnodes_vals, rs.io))
    end
    println_flush(rs.io, "Saved Coq generator to $(path)")
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
    function add_ctor(v::Opt.T{Expr.T})
        push!(constructors_overapproximation, v)
        v
    end
    e = gen_expr(
        rs,
        DistNil(Typ),
        gen_type(rs, p.ty_size, p.param_vars_by_size),
        p.size,
        p.ty_size,
        p.param_vars_by_size,
        add_ctor,
    )
    STLCGeneration(e, constructors_overapproximation)
end

function save_coq_generator(rs, p, s, f)
    path = joinpath(rs.out_dir, "$(s)_Generator.v")
    open(path, "w") do file
        vals = compute(rs.var_vals, values(rs.adnodes_of_interest))
        adnodes_vals = Dict(s => vals[adnode] for (s, adnode) in rs.adnodes_of_interest)
        println(file, f(p, adnodes_vals, rs.io))
    end
    println_flush(rs.io, "Saved Coq generator to $(path)")
end

function generation_params_emit_stats(rs::RunState, p::BespokeSTLCGenerator, s)
    path = joinpath(rs.out_dir, "$(s)_Generator.v")
    if p == BespokeSTLCGenerator(param_vars_by_size=true,size=5,ty_size=2)
        save_coq_generator(rs, p, s, bespoke_stlc_to_coq)
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
    dependents::Vector{Symbol}
    ty_dependents::Vector{Symbol}
    stack_size::Integer
    intwidth::Integer
end
TypeBasedSTLCGenerator(; size, ty_size, dependents, ty_dependents, stack_size, intwidth) =
    TypeBasedSTLCGenerator(size, ty_size, dependents, ty_dependents, stack_size, intwidth)
function to_subpath(p::TypeBasedSTLCGenerator)
    [
        "stlc",
        "typebased",
        "sz=$(p.size)-tysz=$(p.ty_size)",
        "dependents=$(join(Base.map(string, p.dependents),"-"))",
        "ty_dependents=$(join(Base.map(string, p.ty_dependents),"-"))",
        "stack_size=$(p.stack_size)",
        "intwidth=$(p.intwidth)",
    ]
end
function generate(rs::RunState, p::TypeBasedSTLCGenerator)
    constructors_overapproximation = []
    function add_ctor(v::Expr.T)
        push!(constructors_overapproximation, Opt.Some(Expr.T, v))
        v
    end
    e = tb_gen_expr(rs, p, p.size, empty_stack(p), add_ctor)
    STLCGeneration(Opt.Some(Expr.T, e), constructors_overapproximation)
end
function generation_params_emit_stats(rs::RunState, p::TypeBasedSTLCGenerator, s)
    save_coq_generator(rs, p, s, typebased_stlc_to_coq)
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
    SimpleLossMgr(loss, nothing)
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
to_subpath(p::SamplingSTLCConstructorEntropy) = ["sampling_ctor_entropy", "freq=$(p.resampling_frequency)-spb=$(p.samples_per_batch)"]
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

    SimpleLossMgr(loss, nothing)
end

##################################
# BST generation
##################################

abstract type BST <: Benchmark end
struct BSTGeneration <: Generation{BST}
    t::KVTree.T
    constructors_overapproximation::Vector{KVTree.T}
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
    function add_ctor(v::KVTree.T)
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
    leaf_dependents::Vector{Symbol}
    num_dependents::Vector{Symbol}
    intwidth::Integer
end
TypeBasedBSTGenerator(; size, leaf_dependents, num_dependents, intwidth) =
  TypeBasedBSTGenerator(size, leaf_dependents, num_dependents, intwidth)
function to_subpath(p::TypeBasedBSTGenerator)
    [
        "bst",
        "typebased",
        "sz=$(p.size)",
        "leaf_dependents=$(join(Base.map(string, p.leaf_dependents),"-"))",
        "num_dependents=$(join(Base.map(string, p.num_dependents),"-"))",
        "intwidth=$(p.intwidth)",
    ]
end
function generate(rs::RunState, p::TypeBasedBSTGenerator)
    constructors_overapproximation = []
    function add_ctor(v::KVTree.T)
        push!(constructors_overapproximation, v)
        v
    end
    t = typebased_gen_tree(rs, p, p.size, 20, add_ctor)
    BSTGeneration(t, constructors_overapproximation)
end
function generation_params_emit_stats(rs::RunState, p::TypeBasedBSTGenerator, s)
    save_coq_generator(rs, p, s, typebased_bst_to_coq)
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
# RBT generation
##################################

abstract type RBT <: Benchmark end
function sandwich(::Type{RBT})
    (
        "Require Import ZArith.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.
Import MonadNotation.
From Coq Require Import List.
Import ListNotations.

From RBT Require Import Impl Spec.",
"(* --------------------- Tests --------------------- *)

Definition test_prop_InsertValid :=  
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun v =>
        (prop_InsertValid t k v)))).

(*! QuickChick test_prop_InsertValid. *)

Definition test_prop_DeleteValid :=  
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
        prop_DeleteValid t k)).

(*! QuickChick test_prop_DeleteValid. *)

Definition test_prop_InsertPost :=  
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
     forAll arbitrary (fun v =>
        prop_InsertPost t k k' v)))).

(*! QuickChick test_prop_InsertPost. *)

Definition test_prop_DeletePost := 
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
        prop_DeletePost t k k'))).

(*! QuickChick test_prop_DeletePost. *)
    
Definition test_prop_InsertModel :=  
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun v =>
        prop_InsertModel t k v))).

(*! QuickChick test_prop_InsertModel. *)
    
Definition test_prop_DeleteModel :=  
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
            prop_DeleteModel t k)).

(*! QuickChick test_prop_DeleteModel. *)

Definition test_prop_InsertInsert :=  
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v =>
    forAll arbitrary (fun v' =>     
        prop_InsertInsert t k k' v v'))))).

(*! QuickChick test_prop_InsertInsert. *)
    
Definition test_prop_InsertDelete := 
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v =>
        prop_InsertDelete t k k' v)))).

(*! QuickChick test_prop_InsertDelete. *)
    
Definition test_prop_DeleteInsert := 
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v' =>
        prop_DeleteInsert t k k' v')))).

(*! QuickChick test_prop_DeleteInsert. *)
    
Definition test_prop_DeleteDelete :=  
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
        prop_DeleteDelete t k k'))).

(*! QuickChick test_prop_DeleteDelete. *)
          "
    )
end


struct RBTGeneration <: Generation{RBT}
    t::ColorKVTree.t
end
function generation_emit_stats(::RunState, g::RBTGeneration, s::String)
end
value(g::RBTGeneration) = g.t

##################################
# Type-based RBT generator
##################################

struct TypeBasedRBTGenerator <: GenerationParams{RBT}
    size::Integer
    leaf_dependents::Vector{Symbol}
    red_dependents::Vector{Symbol}
    num_dependents::Vector{Symbol}
    stack_size::Integer
    intwidth::Integer
end
TypeBasedRBTGenerator(; size, leaf_dependents, red_dependents, num_dependents, stack_size, intwidth) =
    TypeBasedRBTGenerator(size, leaf_dependents, red_dependents, num_dependents, stack_size, intwidth)
function to_subpath(p::TypeBasedRBTGenerator)
    [
        "rbt",
        "typebased",
        "sz=$(p.size)",
        "leaf_dependents=$(join(Base.map(string, p.leaf_dependents),"-"))",
        "red_dependents=$(join(Base.map(string, p.red_dependents),"-"))",
        "num_dependents=$(join(Base.map(string, p.num_dependents),"-"))",
        "stack_size=$(p.stack_size)",
        "intwidth=$(p.intwidth)",
    ]
end
function generate(rs::RunState, p::TypeBasedRBTGenerator)
    RBTGeneration(tb_gen_rbt(rs, p, p.size, Color.Black(), empty_stack(p)))
end
function generation_params_emit_stats(rs::RunState, p::TypeBasedRBTGenerator, s)
    save_coq_generator(rs, p, s, typebased_rbt_to_coq)
end

##################################
# Property loss
##################################

struct SatisfyPropertyLoss{T} <: LossConfig{T}
    property::Property{T}
end
to_subpath(p::SatisfyPropertyLoss) = [name(p.property)]
function create_loss_manager(rs::RunState, p::SatisfyPropertyLoss, generation)
    println_flush(rs.io, "Building computation graph for $(p)...")
    time_build_loss = @elapsed begin
        meets_property = check_property(p.property, value(generation))
        loss = -LogPr(meets_property)
    end
    println(rs.io, "  $(time_build_loss) seconds")
    println(rs.io)

    SimpleLossMgr(loss, nothing)

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

struct STLCWellTyped <: Property{STLC} end
function check_property(::STLCWellTyped, e::Opt.T{Expr.T})
    @assert isdeterministic(e)
    @match e [
        Some(e) -> (@match typecheck(e) [
            Some(_) -> true,
            None() -> false,
        ]),
        None() -> false,
    ]
end
name(::STLCWellTyped)  = "stlcwelltyped"

struct STLCMightType <: Property{STLC} end
function check_property(::STLCMightType, e::Opt.T{Expr.T})
    @assert isdeterministic(e)
    meets = might_typecheck(e)
    # assert this this is strictly weaker than full welltyped
    @assert !check_property(STLCWellTyped(), e) || meets "$(opt_stlc_str(Dice.frombits(e, Dict())))"
    meets
end
name(::STLCMightType)  = "stlcmighttype"


struct STLCVarNumbers <: Property{STLC} end
function check_property(::STLCVarNumbers, e::Opt.T{Expr.T})
    @assert isdeterministic(e)
    meets = var_numberings_good(e)
    # assert this this is strictly weaker than mighttype
    @assert !check_property(STLCMightType(), e) || meets "$(opt_stlc_str(Dice.frombits(e, Dict())))"
    meets
end
name(::STLCVarNumbers)  = "stlcvarnumbers"



struct BSTOrderInvariant <: Property{BST} end
check_property(::BSTOrderInvariant, t::KVTree.T) =
    satisfies_order_invariant(t)
name(::BSTOrderInvariant) = "order"



struct BookkeepingInvariant <: Property{RBT} end
check_property(::BookkeepingInvariant, t::ColorKVTree.t) =
    satisfies_bookkeeping_invariant(t)
name(::BookkeepingInvariant) = "bookkeeping"

struct BalanceInvariant <: Property{RBT} end
check_property(::BalanceInvariant, t::ColorKVTree.t) =
    satisfies_balance_invariant(t)
name(::BalanceInvariant) = "balance"

struct BlackRootInvariant <: Property{RBT} end
check_property(::BlackRootInvariant, t::ColorKVTree.t) =
    satisfies_black_root_invariant(t)
name(::BlackRootInvariant) = "blackroot"

struct OrderInvariant <: Property{RBT} end
check_property(::OrderInvariant, t::ColorKVTree.t) =
    satisfies_order_invariant(t)
name(::OrderInvariant) = "order"

struct MultipleInvariants{T} <: Property{T}
    properties::Vector{<:Property{T}}
end
check_property(p::MultipleInvariants{T}, t) where T = 
    reduce(&, [
        check_property(property, t)
        for property in p.properties
    ])
name(p::MultipleInvariants{T}) where T =
    join([name(property) for property in p.properties], "AND")

struct TrueProperty{T} <: Property{T}
end
check_property(::TrueProperty{T}, _) where T = true
name(::TrueProperty{T}) where T = "trueproperty"

##################################
# Sampling STLC entropy loss
##################################

function SamplingEntropy{T}(; resampling_frequency, samples_per_batch, property, eq, failure_penalty, forgiveness, rand_forgiveness) where T
    SamplingEntropy{T}(resampling_frequency, samples_per_batch, property, eq, failure_penalty, forgiveness, rand_forgiveness)
end

to_subpath(p::SamplingEntropy) = [
    "reinforce_sampling_entropy",
    "freq=$(p.resampling_frequency)-spb=$(p.samples_per_batch)",
    "eq=$(string(p.eq))",
    "prop=$(name(p.property))",
    "failure_penalty=$(p.failure_penalty)",
    "forgiveness=$(p.forgiveness)",
    "rand_forgiveness=$(p.rand_forgiveness)"
]
function create_loss_manager(::RunState, p::SamplingEntropy{T}, g::Generation{T}) where T
    function consider(sample)
        c = check_property(p.property, sample)
        @assert c isa Bool
        c
    end
    SamplingEntropyLossMgr(p, value(g), consider)
end

##################################
# MLE loss
##################################

abstract type Metric{T} end
abstract type TargetDist end

struct MLELossConfig{T} <: LossConfig{T}
    metric::Metric{T}
    target_dist::TargetDist
end
MLELossConfig(; metric::Metric{T}, target_dist) where T = MLELossConfig{T}(metric, target_dist)
to_subpath(p::MLELossConfig) = [name(p.metric), name(p.target_dist)]
function create_loss_manager(rs::RunState, p::MLELossConfig, generation)
    println_flush(rs.io, "Building computation graph for $(p)...")
    time_build_loss = @elapsed begin
        metric = compute_metric(p.metric, generation)
        loss = metric_loss(metric, p.target_dist)
    end
    println(rs.io, "  $(time_build_loss) seconds")
    println(rs.io)

    SimpleLossMgr(loss, nothing)

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

struct RBTDepth <: Metric{RBT} end
compute_metric(::RBTDepth, gen::RBTGeneration) = rbt_depth(gen.t)
name(::RBTDepth) = "rbt_depth"

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