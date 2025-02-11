include("benchmarks.jl")

TAG = "v109_unif_ty"
TAG = "v1110_weighted_se"
TAG = "v112_prettier_unif"
TAG = "v113_prettier_unif"
TAG = "v114_rbt_table"
OUT_TOP_DIR = joinpath(@__DIR__, "../../../tuning-output")

args = ARGS
allow_overwrite = "-f" ∈ args
args = filter(a -> a != "-f", args)
plot_only = "-p" in args
args = filter(a -> a != "-p", args)

if plot_only
    # TAG = "v1110_weighted_se"
end

# plot_only = true

## PARSE ARGS
if isempty(args)
    TAG = "test3"
    allow_overwrite = true
    as = []
    lr = 0.5
    # lang bespoke spec entropy
    g_p = LangBespokeSTLCGenerator(2,1)
    # l_p = [MLELossConfig{STLC}(num_apps, Uniform()) => lr]
    l_p = [SpecEntropy{STLC}(2,200,wellTyped) => lr]
    l_p = [WeightedSpecEntropy{STLC}(2,200,wellTyped,inv_size) => lr]

    # RBT
    # g_p = LangSiblingDerivedGenerator{RBT}(Main.ColorKVTree.t,Pair{Type,Integer}[Main.ColorKVTree.t=>4,Main.Color.t=>0],2,3) 
    # l_p = [SpecEntropy{RBT}(2,200,isRBT)=>0.3]

    # BST
    # g_p = LangSiblingDerivedGenerator{BST}(Main.KVTree.t,Pair{Type,Integer}[Main.KVTree.t=>4],2,3)
    # l_p = [SpecEntropy{BST}(2,200,isBST)=>0.3]

    # uniform type
    g_p = LangSiblingDerivedGenerator{STLC}(Main.Expr.t,Pair{Type,Integer}[Main.Expr.t=>5,Main.Typ.t=>2],2,3)
    l_p = [FeatureSpecEntropy{STLC}(2,200,wellTyped,typecheck_ft,true)=>0.3]


    push!(as, replace(string(g_p), " "=>""))
    push!(as, replace(string(l_p), " "=>""))
    push!(as, string(10))
    push!(as, string(0.1))
    empty!(args)
    append!(args, as)
end

expected_types = [GenerationParams, AbstractVector{<:Pair{<:LossConfig, <:Real}}, Integer, Real]

if length(args) != length(expected_types)
    println("Expected $(length(expected_types)) positional args, got $(length(args))")
    exit(1)
end
evaled_args = []
for (i, (arg, expected_type)) in enumerate(zip(args, expected_types))
    evaled_arg = eval(Meta.parse(arg))
    if !(evaled_arg isa expected_type)
        println("Expected arg $(i) to be $(expected_type), got $(typeof(evaled_arg))")
        exit(1)
    end
    push!(evaled_args, evaled_arg)
end
generation_params, loss_config_weight_pairs, epochs, bound = evaled_args
EPOCHS = epochs
SEED = 0

out_dir = joinpath(
    vcat(
        [OUT_TOP_DIR],
        [TAG],
        to_subpath(generation_params),
        vcat([
            vcat(to_subpath(c), ["$(w)"])
            for (c, w) in loss_config_weight_pairs
        ]...),
        ["epochs=$(epochs)"],
        ["bound=$(bound)"],
    )
)
log_path = joinpath(out_dir, if plot_only "plot.log" else "log.log" end)
if isfile(log_path) && !allow_overwrite
    println("Error: Log already exists at the following path:")
    println(log_path)
    println()
    exit(1)
end
mkpath(out_dir)
rs = RunState(Valuation(), Dict{String,ADNode}(), open(log_path, "w"), out_dir, MersenneTwister(SEED), nothing,generation_params)

println(stderr, "Logging to $(log_path)\n")

commit = strip(cmd_out(Cmd(`git rev-parse --short HEAD`, dir=@__DIR__)))
t = now()
println_loud(rs, "$(t) $(commit) $(ARGS)")
println_loud(rs, "== Config ==")
println_loud(rs, "TAG: $(TAG)")
println_loud(rs, generation_params)
println_loud(rs, loss_config_weight_pairs)
println_loud(rs, "Epochs: $(epochs)")
println_loud(rs, "Bound: $(bound)")
println_loud(rs, "SEED: $(SEED)")
println_loud(rs, "ARGS: $(join(map(arg -> contains(arg, ' ') ? "\"$(arg)\"" : arg, ARGS), " "))")
println_loud(rs)
println("Logging to $(log_path)")
println()

if !plot_only
    run_benchmark(rs, generation_params, loss_config_weight_pairs, epochs, bound)
end
make_plots(rs, generation_params, loss_config_weight_pairs, epochs, bound)
t′ = now()

println_loud(rs, t′)
println_loud(rs, "Total time elapsed: $(canonicalize(t′ - t))")

println(stderr, log_path)
# include("dump_loss_graph.jl")
