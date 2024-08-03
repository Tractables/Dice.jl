abstract type GenerationParams{T} end
include("lib/lib.jl")

using Plots
using Random

ENV["GKSwstype"] = "100" # prevent plots from displaying

abstract type Benchmark end
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
    epochs::Integer,
    bound::Real,
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

        for (i, (p, lr)) in enumerate(loss_config_weight_pairs)
            if p isa MLELossConfig
                println_flush(rs.io, "Saving $(s) distribution...")
                metric = compute_metric(p.metric, generation)
                time_infer = @elapsed metric_dist = pr_mixed(rs.var_vals)(metric)
                println(rs.io, "  $(time_infer) seconds")
                save_metric_dist(joinpath(rs.out_dir, "loss$(i)_dist_$(name(p.metric))_$(s).csv"), metric_dist; rs.io)
                println(rs.io)
            end
        end

        # if T == STLC
        #     bespoke = generation_params isa LangBespokeSTLCGenerator
        #     samples_to_take = 10_000
        #     println_flush(rs.io, "Taking $(samples_to_take) metric samples $(bespoke)...")

        #     metrics = [NumApps(), TermSize()]
        #     metric_to_cts = Dict(metric => Dict() for metric in metrics)

        #     a = ADComputer(rs.var_vals)
        #     time_sample = @elapsed with_concrete_ad_flips(rs.var_vals, value(generation)) do
        #         for _ in 1:samples_to_take
        #             sample = sample_as_dist(rs.rng, a, value(generation))
        #             is_valid = check_property(STLCWellTyped(), sample)
        #             @assert !bespoke || is_valid
        #             for (metric, cts) in metric_to_cts
        #                 key = (
        #                     is_valid,
        #                     Dice.frombits(
        #                         compute_metric(metric, STLCGeneration(sample,[])),
        #                         Dict())
        #                 )
        #                 get!(cts, key, 0)
        #                 cts[key] += 1
        #             end
        #         end
        #     end
        #     println_loud(rs, "  $(time_sample) seconds")
        #     println_loud(rs, metric_to_cts)

        #     for (metric, cts) in metric_to_cts
        #         filename = joinpath(rs.out_dir, "sampled_$(samples_to_take)_dist_$(name(metric))_$(s).csv")
        #         open(filename, "w") do file
        #             min_metric_val = minimum(
        #                 metric_val
        #                 for (valid, metric_val) in keys(cts)
        #             )
        #             @assert min_metric_val >= 0
        #             max_metric_val = maximum(
        #                 metric_val
        #                 for (valid, metric_val) in keys(cts)
        #             )

        #             valids = if bespoke
        #                 [true] else [true, false] end
        #             println(file, join([
        #                 if valid "$(metric_val)" else "$(metric_val)!" end
        #                 for metric_val in 0:max_metric_val
        #                 for valid in valids
                        
        #             ], "\t"))
        #             println(file, join([
        #                 get(cts, (valid, metric_val), 0)
        #                 for metric_val in 0:max_metric_val
        #                 for valid in valids
        #             ], "\t"))
        #         end
        #     end
        # end

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
    #     println(f, join([d[i] for i in 0:7],"\t"))
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
    keyf::Symbol
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

using Plots

# pgfplotsx()

function save_areaplot(path, v)
    mat = mapreduce(permutedims, vcat, v)
    torow(v) = reshape(v, 1, length(v))
    fontsize=18
    areaplot(
        mat,
        labels=torow(["$(i)" for i in 0:size(mat, 2)]),
        # palette=:lightrainbow)
        palette=cgrad(:thermal),
        tickfontsize=fontsize,
        legendfontsize=fontsize,
        fontfamily="Palatino Roman",
        fontsize=fontsize,
        xlabel="Epochs",
        ylabel="Probability",
        # margin=5Plots.mm,
        xlabelfontsize=fontsize,
        ylabelfontsize=fontsize,
        legend=:outertopright,
    )
    # savefig("$(path).svg")
    savefig("$(path).tikz")
    savefig("$(path).tex")
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

        keyf = if m.p.keyf == :identity identity
        elseif m.p.keyf == :num_apps num_apps
        else error() end

        loss, actual_loss = sum(
            begin
                lpr_eq = LogPr(f_eq(m.val, sample))
                lpr_eq_expanded = Dice.expand_logprs(l, lpr_eq)
                # diff_test_typecheck(sample, Dice.frombits(sample, Dict()))
                meets = m.consider(sample)

                # depth = Dice.frombits(rbt_depth(sample), Dict())

                # @assert meets
                meets && (num_meeting += 1)

                loss_here, actual_loss_here = if meets || (m.p.rand_forgiveness && rand(rs.rng) < m.p.forgiveness)
                    (
                        # 2 ^ depth * 
                        lpr_eq_expanded * compute(a, lpr_eq_expanded),
                        # 2 ^ depth * 
                        lpr_eq_expanded
                    )
                elseif !meets && !m.p.rand_forgiveness
                    @assert false
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

    # N = 3
    # samples_path = joinpath(rs.out_dir, "samples.csv")
    # dist_path = joinpath(rs.out_dir, "dist.csv")
    # if epoch == 1
    #     clear_file(samples_path)
    #     clear_file(dist_path)
    # end
    # d = pr_mixed(rs.var_vals)(m.val)
    # open(dist_path, "a") do f
    #     println(f, join([d[i] for i in 0:2^N-1],"\t"))
    # end
    # open(samples_path, "a") do f
    #     println(f, join([
    #         count(s -> prob_equals(s, DistUInt{N}(i)) === true, m.current_samples)
    #         for i in 0:2^N-1
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
function sandwichmaybestlc()
    (
        "From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.",
"Definition test_prop_SinglePreserve :=
forAllMaybe gSized (fun (e: Expr) =>
  prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)

Definition test_prop_MultiPreserve :=
forAllMaybe gSized (fun (e: Expr) =>
  prop_MultiPreserve e).

(*! QuickChick test_prop_MultiPreserve. *)
          "
    )
end


struct STLCGeneration <: Generation{STLC}
    e::OptExpr.t
    constructors_overapproximation::Vector{OptExpr.t}
end
function generation_emit_stats(rs::RunState, g::STLCGeneration, s::String)
    # println_flush(rs.io, "Saving samples...")
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
    function add_ctor(v::OptExpr.t)
        push!(constructors_overapproximation, v)
        v
    end
    e = generate(rs, p, add_ctor)
    if T == STLC
        STLCGeneration(OptExpr.Some(e), [OptExpr.Some(x) for x in constructors_overapproximation])
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

function save_coq_generator(rs, p, s, f)
    path = joinpath(rs.out_dir, "$(s)_Generator.v")
    open(path, "w") do file
        vals = compute(rs.var_vals, values(rs.adnodes_of_interest))
        adnodes_vals = Dict(s => vals[adnode] for (s, adnode) in rs.adnodes_of_interest)
        println(file, f(p, adnodes_vals, rs.io))
    end
    println_flush(rs.io, "Saved Coq generator to $(path)")
end

unctor = Dict()

module LeafCtorKVTree
    using Dice
    @inductive t LeafCtorKVTree_E()
end
to_coq(::Type{LeafCtorKVTree.t}) = "LeafCtorKVTree"
unctor[LeafCtorKVTree.LeafCtorKVTree_E] = KVTree.E
module CtorKVTree
    using Dice
    @inductive t CtorKVTree_E() CtorKVTree_T()
end
to_coq(::Type{CtorKVTree.t}) = "CtorKVTree"
unctor[CtorKVTree.CtorKVTree_T] = KVTree.T
unctor[CtorKVTree.CtorKVTree_E] = KVTree.E
ctor_tys(::Type{KVTree.t}) = [CtorKVTree.t, LeafCtorKVTree.t]

module LeafCtorColorKVTree
    using Dice
    @inductive t LeafCtorColorKVTree_E()
end
to_coq(::Type{LeafCtorColorKVTree.t}) = "LeafCtorColorKVTree"
unctor[LeafCtorColorKVTree.LeafCtorColorKVTree_E] = ColorKVTree.E
module CtorColorKVTree
    using Dice
    @inductive t CtorColorKVTree_E() CtorColorKVTree_T()
end
to_coq(::Type{CtorColorKVTree.t}) = "CtorColorKVTree"
unctor[CtorColorKVTree.CtorColorKVTree_T] = ColorKVTree.T
unctor[CtorColorKVTree.CtorColorKVTree_E] = ColorKVTree.E
ctor_tys(::Type{ColorKVTree.t}) = [CtorColorKVTree.t, LeafCtorColorKVTree.t]

module LeafCtorColor
    using Dice
    @inductive t LeafCtorColor_R() LeafCtorColor_B()
end
to_coq(::Type{LeafCtorColor.t}) = "LeafCtorColor"
unctor[LeafCtorColor.LeafCtorColor_R] = Color.R
unctor[LeafCtorColor.LeafCtorColor_B] = Color.B
module CtorColor
    using Dice
    @inductive t CtorColor_R() CtorColor_B()
end
to_coq(::Type{CtorColor.t}) = "CtorColor"
ctor_tys(::Type{Color.t}) = [CtorColor.t, LeafCtorColor.t]
unctor[CtorColor.CtorColor_R] = Color.R
unctor[CtorColor.CtorColor_B] = Color.B

module LeafCtorTyp
    using Dice
    @inductive t LeafCtorTyp_TBool()
end
to_coq(::Type{LeafCtorTyp.t}) = "LeafCtorTyp"
unctor[LeafCtorTyp.LeafCtorTyp_TBool] = Typ.TBool
module CtorTyp
    using Dice
    @inductive t CtorTyp_TBool() CtorTyp_TFun()
end
to_coq(::Type{CtorTyp.t}) = "CtorTyp"
unctor[CtorTyp.CtorTyp_TBool] = Typ.TBool
unctor[CtorTyp.CtorTyp_TFun] = Typ.TFun
ctor_tys(::Type{Typ.t}) = [CtorTyp.t, LeafCtorTyp.t]

module LeafCtorExpr
    using Dice
    @inductive t LeafCtorExpr_Var() LeafCtorExpr_Bool()
end
to_coq(::Type{LeafCtorExpr.t}) = "LeafCtorExpr"
unctor[LeafCtorExpr.LeafCtorExpr_Var] = Expr.Var
unctor[LeafCtorExpr.LeafCtorExpr_Bool] = Expr.Bool
module CtorExpr
    using Dice
    @inductive t CtorExpr_Var() CtorExpr_Bool() CtorExpr_Abs() CtorExpr_App()
end
to_coq(::Type{CtorExpr.t}) = "CtorExpr"
unctor[CtorExpr.CtorExpr_Var] = Expr.Var
unctor[CtorExpr.CtorExpr_Bool] = Expr.Bool
unctor[CtorExpr.CtorExpr_Abs] = Expr.Abs
unctor[CtorExpr.CtorExpr_App] = Expr.App
ctor_tys(::Type{Expr.t}) = [CtorExpr.t, LeafCtorExpr.t]

function ctor_ty(ty, leaf)
    inner_ctor_ty, leaf_ctor_ty = ctor_tys(ty)
    if leaf leaf_ctor_ty else inner_ctor_ty end
end


function module_of_func(f)
    @assert all(m.module == methods(f)[1].module for m in methods(f)) "$(f) $(methods(f))"
    methods(f)[1].module
end

function ctor_to_params(f)
    m = module_of_func(f)
    for (ctor, params) in variants(m.t)
        if f == ctor
            return params
        end
    end
    error("ctor_to_params failed $(f) $(m)")
end

ty_is_recursive(ty) = any(ty in params for (ctor, params) in variants(ty))

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
    STLCGeneration(res, [
        interp(rs, gen_expr_lang(size, p.typ_size))[1]
        for size in 0:p.expr_size
    ])
    # STLCGeneration(res, function_results["genExpr"])
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
    @assert length(generation.constructors_overapproximation) == rs.p.expr_size + 1
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
function sandwich(::Type{BST})
    (
        "From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith.
From ExtLib Require Import Monad.
Import MonadNotation.

From BST Require Import Impl.
From BST Require Import Spec.",
"Definition manual_shrink_tree := 
fun x : Tree =>
let
  fix aux_shrink (x' : Tree) : list Tree :=
    match x' with
    | E => []
    | T p0 p1 p2 p3 =>
        ([p0] ++
         map (fun shrunk : Tree => T shrunk p1 p2 p3) (aux_shrink p0) ++
         []) ++
        (map (fun shrunk : nat => T p0 shrunk p2 p3) (shrink p1) ++ []) ++
        (map (fun shrunk : nat => T p0 p1 shrunk p3) (shrink p2) ++ []) ++
        ([p3] ++
         map (fun shrunk : Tree => T p0 p1 p2 shrunk) (aux_shrink p3) ++
         []) ++ []
    end in
aux_shrink x.


#[global]
Instance shrTree : Shrink (Tree) := 
{| shrink x := manual_shrink_tree x |}.

Definition test_prop_InsertValid   :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (v: nat) =>
prop_InsertValid t k v)))
.

(*! QuickChick test_prop_InsertValid. *)

Definition test_prop_DeleteValid   :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat) =>
prop_DeleteValid t k))
.

(*! QuickChick test_prop_DeleteValid. *)


Definition test_prop_UnionValid    :=
forAll gSized (fun (t1: Tree)  =>
forAll gSized (fun (t2: Tree) =>
prop_UnionValid t1 t2))
.

(*! QuickChick test_prop_UnionValid. *)

Definition test_prop_InsertPost    :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (k': nat)  =>
forAll arbitrary (fun (v: nat) =>
prop_InsertPost t k k' v))))
.

(*! QuickChick test_prop_InsertPost. *)

Definition test_prop_DeletePost    :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (k': nat) =>
prop_DeletePost t k k')))
.

(*! QuickChick test_prop_DeletePost. *)

Definition test_prop_UnionPost   :=
forAll gSized (fun (t: Tree)  =>
forAll gSized (fun (t': Tree)  =>
forAll arbitrary (fun (k: nat) =>
prop_UnionPost t t' k)))
.

(*! QuickChick test_prop_UnionPost. *)

Definition test_prop_InsertModel   :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (v: nat) =>
prop_InsertModel t k v)))
.

(*! QuickChick test_prop_InsertModel. *)

Definition test_prop_DeleteModel   :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat) =>
prop_DeleteModel t k))
.

(*! QuickChick test_prop_DeleteModel. *)

Definition test_prop_UnionModel    :=
forAll gSized (fun (t: Tree)  =>
forAll gSized (fun (t': Tree) =>
prop_UnionModel t t'))
.

(*! QuickChick test_prop_UnionModel. *)

Definition test_prop_InsertInsert    :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (k': nat)  =>
forAll arbitrary (fun (v: nat)  =>
forAll arbitrary (fun (v': nat) =>
prop_InsertInsert t k k' v v')))))
.

(*! QuickChick test_prop_InsertInsert. *)

Definition test_prop_InsertDelete    :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (k': nat)  =>
forAll arbitrary (fun (v: nat) =>
prop_InsertDelete t k k' v))))
.

(*! QuickChick test_prop_InsertDelete. *)

Definition test_prop_InsertUnion   :=
forAll gSized (fun (t: Tree)  =>
forAll gSized (fun (t': Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (v: nat) =>
prop_InsertUnion t t' k v))))
.

(*! QuickChick test_prop_InsertUnion. *)

Definition test_prop_DeleteInsert    :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (k': nat)  =>
forAll arbitrary (fun (v': nat) =>
prop_DeleteInsert t k k' v'))))
.

(*! QuickChick test_prop_DeleteInsert. *)

Definition test_prop_DeleteDelete    :=
forAllShrink gSized shrink (fun (t: Tree)  =>
forAllShrink arbitrary shrink (fun (k: nat)  =>
forAllShrink arbitrary shrink (fun (k': nat) =>
whenFail' (fun tt => show (t, k, k', delete k t, delete k' t, delete k (delete k' t), delete k' (delete k t)))
(prop_DeleteDelete t k k'))))
.

(*! QuickChick test_prop_DeleteDelete. *)

Definition test_prop_DeleteUnion   :=
forAll gSized (fun (t: Tree)  =>
forAll gSized (fun (t': Tree)  =>
forAll arbitrary (fun (k: nat) =>
prop_DeleteUnion t t' k)))
.

(*! QuickChick test_prop_DeleteUnion. *)

Definition test_prop_UnionDeleteInsert   :=
forAll gSized (fun (t :Tree)  =>
forAll gSized (fun (t': Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (v: nat) =>
prop_UnionDeleteInsert t t' k v))))
.

(*! QuickChick test_prop_UnionDeleteInsert. *)

Definition test_prop_UnionUnionIdem    :=
forAll gSized (fun (t: Tree) =>
prop_UnionUnionIdem t)
.

(*! QuickChick test_prop_UnionUnionIdem. *)

Definition test_prop_UnionUnionAssoc   :=
forAll gSized (fun (t1: Tree)  =>
forAll gSized (fun (t2: Tree)  =>
forAll gSized (fun (t3: Tree) =>
prop_UnionUnionAssoc t1 t2 t3)))
.

(*! QuickChick test_prop_UnionUnionAssoc. *)
     "
    )
end


struct BSTGeneration <: Generation{BST}
    t::KVTree.t
    constructors_overapproximation::Vector{KVTree.t}
end
function generation_emit_stats(rs::RunState, g::BSTGeneration, s::String)
end
value(g::BSTGeneration) = g.t


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
function check_property(::STLCWellTyped, e::OptExpr.t)
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
function check_property(::STLCMightType, e::OptExpr.t)
    @assert isdeterministic(e)
    meets = might_typecheck(e)
    # assert this this is strictly weaker than full welltyped
    @assert !check_property(STLCWellTyped(), e) || meets "$(opt_stlc_str(Dice.frombits(e, Dict())))"
    meets
end
name(::STLCMightType)  = "stlcmighttype"


struct STLCMayType <: Property{STLC} end
function check_property(::STLCMayType, e::OptExpr.t)
    @assert isdeterministic(e)
    meets = may_typecheck(e)
    # assert this this is strictly weaker than might type
    @assert !check_property(STLCMightType(), e) || meets "$(opt_stlc_str(Dice.frombits(e, Dict())))"
    @assert check_property(STLCMightType(), rem_num_bools(e)) == meets "eq to might rem $(opt_stlc_str(Dice.frombits(e, Dict())))"

    # only applies when arbitrary_prims = true
    # @assert check_property(STLCMightType(), e) == meets "eq to might rem $(opt_stlc_str(Dice.frombits(e, Dict())))"
    meets
end
name(::STLCMayType)  = "stlcmaytype"

struct STLCVarNumbers <: Property{STLC} end
function check_property(::STLCVarNumbers, e::OptExpr.t)
    @assert isdeterministic(e)
    meets = var_numberings_good(e)
    # assert this this is strictly weaker than mighttype
    @assert !check_property(STLCMightType(), e) || meets "$(opt_stlc_str(Dice.frombits(e, Dict())))"
    meets
end
name(::STLCVarNumbers)  = "stlcvarnumbers"



struct BSTOrderInvariant <: Property{BST} end
check_property(::BSTOrderInvariant, t::KVTree.t) =
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

rbt_property() = MultipleInvariants([
    BookkeepingInvariant(),
    BalanceInvariant(),
    OrderInvariant(),
])

##################################
# Sampling STLC entropy loss
##################################

function SamplingEntropy{T}(; resampling_frequency, samples_per_batch, property, eq, failure_penalty, forgiveness, rand_forgiveness, keyf) where T
    SamplingEntropy{T}(resampling_frequency, samples_per_batch, property, eq, failure_penalty, forgiveness, rand_forgiveness, keyf)
end

to_subpath(p::SamplingEntropy) = [
    "reinforce_sampling_entropy",
    "freq=$(p.resampling_frequency)-spb=$(p.samples_per_batch)",
    "eq=$(string(p.eq))",
    "prop=$(name(p.property))",
    "failure_penalty=$(p.failure_penalty)",
    "forgiveness=$(p.forgiveness)",
    "rand_forgiveness=$(p.rand_forgiveness)",
    "keyf=$(p.keyf)",
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
end

struct RBTDepth <: Metric{RBT} end
compute_metric(::RBTDepth, gen::RBTGeneration) = rbt_depth(gen.t)
name(::RBTDepth) = "rbt_depth"

struct RBTSize <: Metric{RBT} end
compute_metric(::RBTSize, gen::RBTGeneration) = tree_size(gen.t)
name(::RBTSize) = "rbt_size"

struct BSTDepth <: Metric{BST} end
compute_metric(::BSTDepth, gen::BSTGeneration) = bst_depth(gen.t)
name(::BSTDepth) = "bst_depth"

struct TreeSize <: Metric{BST} end
compute_metric(::TreeSize, gen::BSTGeneration) = tree_size(gen.t)
name(::TreeSize) = "tree_size"

struct NumApps <: Metric{STLC} end
compute_metric(::NumApps, gen::STLCGeneration) = num_apps(gen.e)
name(::NumApps) = "num_apps"

struct STLCDepth <: Metric{STLC} end
compute_metric(::STLCDepth, gen::STLCGeneration) = depth(gen.e)
name(::STLCDepth) = "stlc_depth"

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