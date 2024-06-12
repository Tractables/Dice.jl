include("benchmarks.jl")

TAG = "v45_stlcmayarb"
TAG = "v46_tbmay"
TAG = "v48_bst_lang"
TAG = "v49_stlcmaythin"
TAG = "v50_stlcbound"
TAG = "v51_rbtbound"
OUT_TOP_DIR = "/space/tjoa/tuning-output"

## PARSE ARGS
if isempty(ARGS)
    TAG = "test2"
    as = ["-f"]
    # g_p = TypeBasedBSTGenerator(
    #     size=5,
    #     leaf_dependents=[:size,:last_callsite],
    #     num_dependents=[:size,:last_callsite],
    #     intwidth=6,
    # )
    # g_p = DerivedGenerator{RBT}(
    #     root_ty=ColorKVTree.t,
    #     ty_sizes=Dict(ColorKVTree.t=>4, Color.t=>0),
    #     stack_size=1,
    #     intwidth=6,
    # )
    g_p = TypeBasedSTLCGenerator(
        size=2,
        ty_size=1,
        dependents=[:size,:stack_tail],
        ty_dependents=[:size,:stack_tail],
        stack_size=2,
        intwidth=6,
    )
    # g_p = TypeBasedRBTGenerator(
    #     size=3,
    #     leaf_dependents=[:size,:parent_color,:stack_tail],
    #     red_dependents=[:size,:parent_color,:stack_tail],
    #     num_dependents=[:size,:parent_color,:stack_tail],
    #     stack_size=2,
    #     intwidth=6,
    # )
    lr = 0.5
    fp = 0
    g_p = LangDerivedGenerator{BST}(
        root_ty=KVTree.t,
        ty_sizes=[KVTree.t=>5],
        stack_size=2,
        intwidth=6,
        arbitrary_prims=false,
    )
    # g_p = LangBespokeSTLCGenerator(
    #     expr_size=2,
    #     typ_size=1,
    # )
    l_p = [
        # SamplingEntropy{STLC}(
        #     resampling_frequency=1,
        #     samples_per_batch=50,
        #     property=STLCMightType(),
        #     eq=:eq_structure,
        #     failure_penalty=fp,
        #     forgiveness=0,
        #     rand_forgiveness=true,
        # ) => lr,
        SamplingEntropy{BST}(
            resampling_frequency=1,
            samples_per_batch=50,
            property=BSTOrderInvariant(),
            eq=:prob_equals,
            failure_penalty=fp,
            forgiveness=0,
            rand_forgiveness=true,
        ) => lr,

        # ApproxSTLCConstructorEntropy() => lr,
        # MLELossConfig{STLC}(NumApps(), Linear()) => lr,
    ]


    # g_p = LangSiblingDerivedGenerator{RBT}(
    #     root_ty=ColorKVTree.t,
    #     ty_sizes=[ColorKVTree.t=>2, Color.t=>0],
    #     stack_size=2,
    #     intwidth=6,
    # )
    # l_p = [
    #     SamplingEntropy{RBT}(
    #         resampling_frequency=1,
    #         samples_per_batch=50,
    #         property=MultipleInvariants([
    #             BookkeepingInvariant(),
    #             BalanceInvariant(),
    #             OrderInvariant(),
    #         ]),
    #         eq=:prob_equals,
    #         failure_penalty=fp,
    #         forgiveness=0.1,
    #         rand_forgiveness=false,
    #     ) => lr,
    # ]



    push!(as, replace(string(g_p), " "=>""))
    push!(as, replace(string(l_p), " "=>""))
    push!(as, string(10))
    push!(as, string(0.1))
    empty!(ARGS)
    append!(ARGS, as)
end

expected_types = [GenerationParams, AbstractVector{<:Pair{<:LossConfig, <:Real}}, Integer, Real]

args = ARGS
allow_overwrite = "-f" ∈ args
args = filter(a -> a != "-f", args)
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
log_path = joinpath(out_dir, "log.log")
if isfile(log_path) && !allow_overwrite
    println("Error: Log already exists at the following path:")
    println(log_path)
    println()
    exit(1)
end
mkpath(out_dir)
rs = RunState(Valuation(), Dict{String,ADNode}(), open(log_path, "w"), out_dir, MersenneTwister(SEED), nothing)

println(stderr, "Logging to $(log_path)\n")

commit = strip(cmd_out(`git rev-parse --short HEAD`))
t = now()
println_loud(rs, "$(t) $(commit) $(ARGS)")
println_loud(rs, "== Config ==")
println_loud(rs, "TAG: $(TAG)")
println_loud(rs, generation_params)
println_loud(rs, loss_config_weight_pairs)
println_loud(rs, "Epochs: $(epochs)")
println_loud(rs, "Bound: $(bound)")
println_loud(rs, "DistNat: $(DistNat)")
println_loud(rs, "SEED: $(SEED)")
println_loud(rs)
println("Logging to $(log_path)")
println()

run_benchmark(rs, generation_params, loss_config_weight_pairs, epochs, bound)
t′ = now()

println_loud(rs, t′)
println_loud(rs, "Total time elapsed: $(canonicalize(t′ - t))")

println(stderr, log_path)
# include("dump_loss_graph.jl")