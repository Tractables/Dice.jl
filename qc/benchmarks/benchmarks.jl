abstract type GenerationParams{T} end
include("lib/lib.jl")

UNIQUE_CURVES_SAMPLES = 10_000
using Plots
using Random
using Infiltrator
using DataStructures
using JLD2
# using Debugger

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

    press = [
        if m isa FeatureSpecEntropyLossMgr
            feature_unique_curve(rs, m, UNIQUE_CURVES_SAMPLES)
        else nothing end
        for m in loss_mgrs
    ]

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
            if m isa SpecEntropyLossMgr || m isa FeatureSpecEntropyLossMgr || m isa WeightedSpecEntropyLossMgr
                a = ADComputer(Valuation())
                a.vals = vals
                al_val = compute(a, m.current_actual_loss)
                push!(al_curves[i], al_val)
            end
        end

        if any(isinf(vals[loss]) || isnan(vals[loss]) for loss in losses)
            println_loud(rs, "stopping in epoch $(epoch)")
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

    postss = [
        if m isa FeatureSpecEntropyLossMgr
            feature_unique_curve(rs, m, UNIQUE_CURVES_SAMPLES)
        else nothing end
        for m in loss_mgrs
    ]

    for (loss_config, curve) in zip(loss_configs, curves)
        save_learning_curve(rs.out_dir, curve, join(to_subpath(loss_config), "_"))
    end

    for (al_curve, loss_config, m) in zip(al_curves, loss_configs, loss_mgrs)
        if m isa SpecEntropyLossMgr || m isa FeatureSpecEntropyLossMgr || m isa WeightedSpecEntropyLossMgr
            save_learning_curve(out_dir, al_curve, "actual_loss_" * join(to_subpath(loss_config), "_"))
            save_learning_curve(out_dir, m.num_meeting, "meets_invariant_" * join(to_subpath(loss_config), "_"))
        end
    end

    for (loss_config, pres, posts, m) in zip(loss_configs, press, postss, loss_mgrs)
        if loss_config isa FeatureSpecEntropy
            d = compute_feature_counts(m.feature_counts_history)
            filename = joinpath(rs.out_dir, "feature_dist_" * join(to_subpath(loss_config), "_"))
            save_feature_cts(filename, d)
        end
    end

    save_object(joinpath(out_dir, "pres_posts.jld2"), (press, postss))
end

using PyPlot


begin

function mk_areaplot2(path; xlabel, ylabel, has_header)
    open(path, "r") do f
        header, lines = if has_header
            line, lines... = readlines(f)
            split(line,"\t"), lines
        else
            nothing, readlines(f)
        end
        v = [[parse(Float64, s) for s in split(line,"\t")] for line in lines]
        save_areaplot2(path, header, v; xlabel, ylabel)
    end
end

function save_areaplot2(path, header, v; xlabel, ylabel)
    mat = mapreduce(permutedims, vcat, v)
    torow(v) = reshape(v, 1, length(v))

    labels = if isnothing(header)
        torow(["$(i)" for i in 0:size(mat, 2)])
    else
        function f(h::AbstractString)
            l = 20
            if length(collect(h)) > l
                first(h, l) * " ..."
            else
                h
            end
        end
        torow([
            if i > 50 "" else f(s) end
            for (i, s) in enumerate(header)
        ])
    end

    fontsize=8
    areaplot(
        mat,
        labels=labels,
        palette=cgrad(:thermal),
        tickfontsize=fontsize,
        legendfontsize=fontsize,
        fontfamily="Palatino Roman",
        fontsize=fontsize,
        xlabel=xlabel,
        ylabel=ylabel,
        xlabelfontsize=fontsize,
        ylabelfontsize=fontsize,
        legend=:outerright,
        left_margin=5Plots.mm,
        right_margin=15Plots.mm,
        foreground_color_legend = nothing,
        bottom_margin=5Plots.mm,
        legend_left_margin=-5Plots.mm,
    )
    plot!(size=(1000,500))
    Plots.savefig("$(path).png")
    Plots.savefig("$(path).svg")
end


    # p = plot(
    #     legend=:right,
    #     legendfontsize=fontsize,
    #     fontfamily="Palatino Roman",
    #     foreground_color_legend=nothing,  # transparent background
    #     background_color_legend=nothing,   # transparent background
    #     showaxis=false,                   # hide axes
    #     grid=false,                       # hide grid
    #     ticks=nothing,                    # hide ticks
    #     framestyle=:none                  # hide frame
    # )
    
    # # Add dummy series just for the legend entries
    # for (i, label) in enumerate(header)
    #     plot!(p, [], [], 
    #         label=label,
    #         color=get(cgrad(:thermal), (i-1)/(length(header)-1))
    #     )
    # end
    
    # # Save just the legend
    # savefig("$(path).legend.png")
    # savefig("$(path).legend.svg")

    # savefig("$(path).tikz")
    # savefig("$(path).tex")
using PyPlot





# function save_areaplot2(path, header, v; xlabel, ylabel)
#     mat = mapreduce(permutedims, vcat, v)
    
#     # Normalize each row to get proportions
#     row_sums = sum(mat, dims=2)
#     mat = mat ./ row_sums
    
#     torow(v) = reshape(v, 1, length(v))
#     size = Base.size
    
#     # Generate labels first
#     labels = if isnothing(header)
#         ["$(i)" for i in 0:size(mat)[2]]
#     else
#         function f(h::AbstractString)
#             l = 20
#             if length(collect(h)) > l
#                 first(h, l) * " ..."
#             else
#                 h
#             end
#         end
#         [f(s) for s in header]
#     end
    
#     # Set first label manually
#     if length(labels) > 0
#         labels[1] = "Not well-typed"
#     end
#     for i in 1:length(labels)
#         labels[i] = ""
#     end
    
#     # Threshold for "small" areas (using proportion threshold)
#     threshold = 0.0  # 1% threshold
    
#     # Identify which columns are "small" based on their maximum proportion
#     column_maxes = [maximum(mat[:, i]) for i in 1:size(mat)[2]]
#     is_small = column_maxes .< threshold
    
#     # Combine columns keeping originals but marking small ones for special coloring
#     mat_combined = mat
    
#     # Update labels
#     labels_main = copy(labels)
#     other_indices = findall(is_small)
    
#     # Create figure and axis
#     fig, ax = subplots(figsize=(10, 5))
    
#     # Get x values
#     x = 1:size(mat)[1]
    
#     # Create colors using thermal colormap, skipping first 20%
#     n_main = sum(.!is_small)
#     thermal_cmap = plt.cm.get_cmap("magma")  # similar to thermal
#     main_colors = [(0, 0, 0, 1)]  # Start with black for "Not well-typed"
#     if n_main > 1
#         # Generate colors from thermal gradient, skipping first 20%
#         thermal_colors = [thermal_cmap(i) for i in LinRange(0.2, 1.0, n_main-1)]
#         main_colors = vcat(main_colors, thermal_colors)
#     end
    
#     # Define two shades of blue for "other" categories
#     light_blue = (0.6, 0.8, 1.0, 1.0)  # Light blue
#     dark_blue = (0.2, 0.4, 0.8, 1.0)   # Dark blue
    
#     # Create color array
#     colors = Vector{Tuple{Float64, Float64, Float64, Float64}}(undef, size(mat)[2])
#     main_idx = 1
#     for i in 1:size(mat)[2]
#         if is_small[i]
#             colors[i] = i % 2 == 0 ? light_blue : dark_blue
#             labels_main[i] = "Other"
#         else
#             colors[i] = main_colors[main_idx]
#             main_idx += 1
#         end
#     end
    
#     # Create stacked area plot
#     y_stack = zeros(size(mat_combined)[1])
#     areas = []
    
#     # Track if we've added "Other" to legend
#     other_in_legend = false
    
#     for i in 1:size(mat_combined)[2]
#         # For small categories, only add to legend once
#         if is_small[i]
#             if !other_in_legend
#                 area = ax.fill_between(x, y_stack, y_stack .+ mat_combined[:, i],
#                                      label="Other",
#                                      color=colors[i],
#                                      alpha=0.95)
#                 other_in_legend = true
#             else
#                 area = ax.fill_between(x, y_stack, y_stack .+ mat_combined[:, i],
#                                      color=colors[i],
#                                      alpha=0.95)
#             end
#         else
#             area = ax.fill_between(x, y_stack, y_stack .+ mat_combined[:, i],
#                                  label=labels_main[i],
#                                  color=colors[i],
#                                  alpha=0.95)
#         end
#         push!(areas, area)
#         y_stack .+= mat_combined[:, i]
#     end
    
#     # Style improvements
#     ax.set_facecolor("white")
#     fig.patch.set_facecolor("white")
    
#     # Customize plot
#     fontsize = 8
#     ax.set_xlabel(xlabel, fontsize=fontsize)
#     ax.set_ylabel("Proportion", fontsize=fontsize)
#     ax.tick_params(labelsize=fontsize)
    
#     # Set y-axis to show percentages
#     ax.yaxis.set_major_formatter(plt.matplotlib.ticker.PercentFormatter(1.0))
    
#     # Set font family
#     plt.rcParams["font.family"] = "Palatino"
    
#     # Adjust legend
#     legend = ax.legend(bbox_to_anchor=(1.05, 1),
#                       loc="upper left",
#                       fontsize=fontsize)
#     legend.get_frame().set_facecolor("none")
    
#     # Adjust margins
#     plt.subplots_adjust(left=0.1, right=0.85, bottom=0.1, top=0.9)
    
#     # Save figures
#     plt.savefig("$(path).png", dpi=300, bbox_inches="tight")
#     plt.savefig("$(path).svg", bbox_inches="tight")
    
#     plt.close()
# end





function make_plots(
    rs::RunState,
    generation_params::GenerationParams{T},
    loss_config_weight_pairs::AbstractVector{<:Pair{<:LossConfig{T}, <:Real}},
    epochs::Integer,
    bound::Real,
) where T
    press, postss = load_object(joinpath(out_dir, "pres_posts.jld2"))

    loss_configs, loss_weights = zip(loss_config_weight_pairs...)

    for (loss_config, pres, posts) in zip(loss_configs, press, postss)
        if loss_config isa FeatureSpecEntropy
            name = "unique_curves_" * join(to_subpath(loss_config), "_")
            open(joinpath(out_dir, "$(name).csv"), "w") do file
                xs = 1:length(pres)
                for (num_samples, pre, post) in zip(xs, pres, posts)
                    println(file, "$(num_samples)\t$(pre)\t$(post)")
                end
                Plots.plot(xs, pres, label="Initial", color=:blue, xlabel="Number of samples", ylabel="Count", title="STLC: Cumulative unique types during sampling", legend=:topright)
                plot!(xs, posts, label="Trained", color=:red)
                Plots.savefig(joinpath(out_dir, "$(name).svg"))
            end

            filename = joinpath(rs.out_dir, "feature_dist_" * join(to_subpath(loss_config), "_"))
            mk_areaplot2(filename, has_header=true, xlabel="Sampling #", ylabel="Counts")
        end
    end
end


# make_plots(rs, generation_params, loss_config_weight_pairs, epochs, bound)
end

function compute_feature_counts(feature_counts_history)
    d = []
    for (k, cts) in feature_counts_history
        ctor, args = k
        if ctor == :Some
            ty, = args
            push!(d, (ty_str(ty), cts))
        else 
            ctor = :None
            push!(d, ("not well-typed", cts))
        end
    end
    sort!(d, by=kv -> -sum(kv[2]))
end

function save_feature_cts(filename, d)
    open(filename, "w") do file
        println(file, join([
            k for (k, cts) in d
        ], "\t"))
        for i in 1:length(first(d)[2])
            println(file, join([
                cts[i] for (k, cts) in d
            ], "\t"))
        end
    end
    println_flush(rs.io, "Saved to $(filename)")
    println_flush(rs.io)
end



function generation_params_emit_stats(rs::RunState, generation_params, s)
    println_flush(rs.io, "Default generation_params_emit_stats")
    println_flush(rs.io)
end

######################################################################
# Shared utils (to_dist, areaplots), stuff that belongs elsewhere
######################################################################

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

function typecheck_ft(e::Expr.t)
    @assert isdeterministic(e)
    Dice.frombits(typecheck(e), Dict())
end


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
    Plots.savefig("$(path).tikz")
    Plots.savefig("$(path).tex")
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

function save_learning_curve(out_dir, learning_curve, name)
    open(joinpath(out_dir, "$(name).csv"), "w") do file
        xs = 0:length(learning_curve)-1
        for (epoch, logpr) in zip(xs, learning_curve)
            println(file, "$(epoch)\t$(logpr)")
        end
        Plots.plot(xs, learning_curve)
        Plots.savefig(joinpath(out_dir, "$(name).svg"))
    end
end


######################################################################
# Simple loss mgr
######################################################################

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

######################################################################
# SpecEntropy
######################################################################

struct SpecEntropy{T} <: LossConfig{T}
    resampling_frequency::Integer
    samples_per_batch::Integer
    property::Function
end
function SpecEntropy{T}(; resampling_frequency, samples_per_batch, property) where T
    SpecEntropy{T}(resampling_frequency, samples_per_batch, property)
end
to_subpath(p::SpecEntropy) = [
    "spec_entropy",
    "freq=$(p.resampling_frequency)-spb=$(p.samples_per_batch)",
    "prop=$(p.property)",
]

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

function create_loss_manager(::RunState, p::SpecEntropy{T}, g::Generation) where T
    function consider(sample)
        c = p.property(sample)
        @assert c isa Bool
        c
    end
    SpecEntropyLossMgr(p, g, consider)
end


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
                lpr_eq = LogPr(prob_equals(m.generation.value, sample))
                lpr_eq = Dice.expand_logprs(l, lpr_eq)
                [lpr_eq * compute(a, lpr_eq), Dice.Constant(lpr_eq)]
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



######################################################################
# WeightedSpecEntropy
######################################################################

struct WeightedSpecEntropy{T} <: LossConfig{T}
    resampling_frequency::Integer
    samples_per_batch::Integer
    property::Function
    weighter::Function # deterministic Dice.Dist -> number
end
function WeightedSpecEntropy{T}(; resampling_frequency, samples_per_batch, property, weighter) where T
    WeightedSpecEntropy{T}(resampling_frequency, samples_per_batch, property, weighter)
end
to_subpath(p::WeightedSpecEntropy) = [
    "weighted_spec_entropy",
    "freq=$(p.resampling_frequency)-spb=$(p.samples_per_batch)",
    "prop=$(p.property)",
    "weighter=$(nameof(p.weighter))",
]

mutable struct WeightedSpecEntropyLossMgr <: LossMgr
    p::WeightedSpecEntropy
    generation
    consider
    num_meeting
    current_loss::Union{Nothing,ADNode}
    current_actual_loss::Union{Nothing,ADNode}
    current_samples
    WeightedSpecEntropyLossMgr(p, val, consider) = new(p, val, consider, [], nothing, nothing, nothing)
end

function create_loss_manager(::RunState, p::WeightedSpecEntropy{T}, g::Generation) where T
    function consider(sample)
        c = p.property(sample)
        @assert c isa Bool
        c
    end
    WeightedSpecEntropyLossMgr(p, g, consider)
end


function produce_loss(rs::RunState, m::WeightedSpecEntropyLossMgr, epoch::Integer)
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
                lpr_eq = LogPr(prob_equals(m.generation.value, sample))
                lpr_eq = Dice.expand_logprs(l, lpr_eq)
                w = Dice.Constant(m.p.weighter(sample))
                [w * lpr_eq * compute(a, lpr_eq), w * lpr_eq]
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




######################################################################
# FeatureSpecEntropy
######################################################################

struct FeatureSpecEntropy{T} <: LossConfig{T}
    resampling_frequency::Integer
    samples_per_batch::Integer
    property::Function
    feature::Function # deterministic Dice.Dist -> Hashable 
    train_feature::Bool
end
function FeatureSpecEntropy{T}(; resampling_frequency, samples_per_batch, property, feature, train_feature) where T
    FeatureSpecEntropy{T}(resampling_frequency, samples_per_batch, property, feature, train_feature)
end
to_subpath(p::FeatureSpecEntropy) = [
    "feature_spec_entropy",
    "train_feature=$(p.train_feature)",
    "freq=$(p.resampling_frequency)-spb=$(p.samples_per_batch)",
    "prop=$(p.property)",
    "feature=$(p.feature)",
]

mutable struct FeatureSpecEntropyLossMgr <: LossMgr
    p::FeatureSpecEntropy
    generation
    consider
    num_meeting
    current_loss::Union{Nothing,ADNode}
    current_actual_loss::Union{Nothing,ADNode}
    current_samples
    feature_counts_history
    feature_unique_curve_history
    epochs_history # per resampling
    num_resamples
    FeatureSpecEntropyLossMgr(p, val, consider) = new(p, val, consider, [], nothing, nothing, nothing, Dict(), [], [], 0)
end

function create_loss_manager(::RunState, p::FeatureSpecEntropy{T}, g::Generation) where T
    function consider(sample)
        c = p.property(sample)
        @assert c isa Bool
        c
    end
    FeatureSpecEntropyLossMgr(p, g, consider)
end


function only_first_last!(v)
    if length(v) > 2
        a = first(v)
        b = last(v)
        empty!(v)
        append!(v, [a, b])
    end
end

function feature_unique_curve(rs, m::FeatureSpecEntropyLossMgr, n)
    sampler = sample_from_lang(rs, m.generation.prog)
    a = ADComputer(rs.var_vals)
    samples = [to_dist(sampler()) for _ in 1:n]
    feature_unique_curve = []
    feature_counts = DefaultDict(0)
    # counter(f, collection)
    for s in samples
        s_feature = m.p.feature(s)
        if !haskey(feature_counts, s_feature)
            feature_counts[s_feature] = 0
        end
        feature_counts[s_feature] += 1
        push!(feature_unique_curve, length(feature_counts))
    end
    feature_unique_curve
end

function produce_loss(rs::RunState, m::FeatureSpecEntropyLossMgr, epoch::Integer)
    if (epoch - 1) % m.p.resampling_frequency == 0
        sampler = sample_from_lang(rs, m.generation.prog)
        a = ADComputer(rs.var_vals)
        samples = [to_dist(sampler()) for _ in 1:m.p.samples_per_batch]

        feature_unique_curve = []
        feature_counts = DefaultDict(0)
        # counter(f, collection)
        for s in samples
            s_feature = m.p.feature(s)
            if !haskey(feature_counts, s_feature)
                feature_counts[s_feature] = 0
            end
            feature_counts[s_feature] += 1
            push!(feature_unique_curve, length(feature_counts))
        end

        l = Dice.LogPrExpander(WMC(BDDCompiler([
            prob_equals(m.generation.value,sample)
            for sample in samples
        ])))

        num_meeting = 0
        loss, actual_loss = sum(
            if m.consider(sample)
                num_meeting += 1

                lpr_eq = LogPr(prob_equals(m.generation.value, sample))
                lpr_eq = Dice.expand_logprs(l, lpr_eq)
                ct = feature_counts[m.p.feature(sample)]
                @assert ct != 0 
                rat = ct/length(samples)
                empirical_feature_logpr = Dice.Constant(log(rat))
                if m.p.train_feature
                    [lpr_eq * empirical_feature_logpr, empirical_feature_logpr]
                else
                    [lpr_eq * compute(a, lpr_eq), empirical_feature_logpr]
                end
            else
                [Dice.Constant(0), Dice.Constant(0)]
            end
            for sample in samples
        )
        push!(m.num_meeting, num_meeting / length(samples))

        # loss = Dice.expand_logprs(l, loss) / length(samples)
        loss = loss / length(samples)
        actual_loss = actual_loss / length(samples)
        m.current_loss = loss
        m.current_actual_loss = actual_loss
        m.current_samples = samples

        for feature in keys(feature_counts)
            if !haskey(m.feature_counts_history, feature)
                m.feature_counts_history[feature] = zeros(Int, m.num_resamples)
            end
        end
        for feature in keys(m.feature_counts_history)
            push!(m.feature_counts_history[feature], feature_counts[feature])
        end
        push!(m.feature_unique_curve_history, feature_unique_curve)
        only_first_last!(m.feature_unique_curve_history)
        push!(m.epochs_history, epoch)
        m.num_resamples += 1
    end

    @assert !isnothing(m.current_loss)
    m.current_loss
end

##################################
# Flips
##################################

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

##################################
# MLE loss
##################################

abstract type TargetDist end

struct MLELossConfig{T} <: LossConfig{T}
    metric::Function
    target_dist::TargetDist
end
to_subpath(p::MLELossConfig) = ["mle",string(nameof(p.metric)), name(p.target_dist)]
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