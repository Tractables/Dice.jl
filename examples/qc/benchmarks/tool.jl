include("benchmarks.jl")

TAG = "v21_the_nums"

## PARSE ARGS
if isempty(ARGS)
    TAG = "test"
    as = ["-f"]
    g_p = TypeBasedRBTGenerator(
        size=3,
        leaf_dependents=[:size,:parent_color],
        red_dependents=[:size,:parent_color],
        num_dependents=[:size,:parent_color,:last_callsite],
        intwidth=6,
    )
    lr = 0.01
    fp = 0.01
    l_p = [
            SamplingEntropy{RBT}(
                resampling_frequency=1,
                samples_per_batch=200,
                # property=TrueProperty{RBT}(),
                property=MultipleInvariants([
                    BookkeepingInvariant(),
                    BalanceInvariant(),
                    OrderInvariant(),
                ]),
                failure_penalty=fp,
                ignore_nums=true
            ) => lr,
    ]
    push!(as, replace(string(g_p), " "=>""))
    push!(as, replace(string(l_p), " "=>""))
    push!(as, string(3))
    empty!(ARGS)
    append!(ARGS, as)
end

args = ARGS
allow_overwrite = "-f" ∈ args
args = filter(a -> a != "-f", args)
if length(args) != 3
    println("Expected 3 positional args, got $(length(args))")
    exit(1)
end
expected_types = [GenerationParams, AbstractVector{<:Pair{<:LossConfig, <:Real}}, Integer]
evaled_args = []
for (i, (arg, expected_type)) in enumerate(zip(args, expected_types))
    evaled_arg = eval(Meta.parse(arg))
    if !(evaled_arg isa expected_type)
        println("Expected arg $(i) to be $(expected_type), got $(typeof(evaled_arg))")
        exit(1)
    end
    push!(evaled_args, evaled_arg)
end
generation_params, loss_config_weight_pairs, epochs = evaled_args
EPOCHS = epochs

SEED = 0

out_dir = joinpath(
    vcat(
        ["examples/qc/benchmarks/output"],
        [TAG],
        to_subpath(generation_params),
        vcat([
            vcat(to_subpath(c), ["$(w)"])
            for (c, w) in loss_config_weight_pairs
        ]...),
        ["epochs=$(epochs)"],
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
rs = RunState(Valuation(), Dict{String,ADNode}(), open(log_path, "w"), out_dir, MersenneTwister(SEED))

println(stderr, "Logging to $(log_path)\n")

commit = strip(cmd_out(`git rev-parse --short HEAD`))
t = now()
println_loud(rs, "$(t) $(commit) $(ARGS)")
println_loud(rs, "== Config ==")
println_loud(rs, "TAG: $(TAG)")
println_loud(rs, generation_params)
println_loud(rs, loss_config_weight_pairs)
println_loud(rs, "Epochs: $(epochs)")
println_loud(rs, "DistNat: $(DistNat)")
println_loud(rs, "SEED: $(SEED)")
println_loud(rs)
println("Logging to $(log_path)")
println()

run_benchmark(rs, generation_params, loss_config_weight_pairs, epochs)
t′ = now()

println_loud(rs, t′)
println_loud(rs, "Total time elapsed: $(canonicalize(t′ - t))")

println(stderr, log_path)
# include("dump_loss_graph.jl")