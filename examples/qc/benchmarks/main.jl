include("benchmarks.jl")

GENERATION_PARAMS_LIST = [
    TypeBasedRBTGenerator(size=2, color_by_size=true, learn_leaf_weights=true, use_parent_color=true),
]

LOSS_PARAMS_LIST = [
    SamplingRBTEntropy(
        resampling_frequency=5,
        samples_per_batch=1000,
        additional_loss_params=NullLoss{RBT}(),
        additional_loss_lr=0.,
    ),
    SamplingRBTEntropy(
        resampling_frequency=5,
        samples_per_batch=1000,
        additional_loss_params=SatisfyPropertyLoss(MultipleInvariants([
            BookkeepingInvariant(),
            BalanceInvariant(),
        ])),
        additional_loss_lr=0.0003,
    ),
]

LEARNING_RATE_LIST = [0.3]
EPOCHS_LIST = [20]

SEED = 0
TAG = "pre_v12_neg_refac"

for (
    generation_params, loss_params, learning_rate, epochs
) in Base.product(
    GENERATION_PARAMS_LIST, LOSS_PARAMS_LIST, LEARNING_RATE_LIST, EPOCHS_LIST
)
    out_dir = joinpath(
        vcat(
            ["examples/qc/benchmarks/output"],
            [TAG],
            to_subpath(generation_params),
            to_subpath(loss_params),
            ["epochs=$(epochs)-learning_rate=$(learning_rate)"],
        )
    )
    log_path = joinpath(out_dir, "log.log")
    if isfile(log_path) && "-f" ∉ ARGS
        println("Error: Log already exists at the following path:")
        println(log_path)
        println()
        continue
    end
    mkpath(out_dir)
    rs = RunState(Valuation(), Dict{String,ADNode}(), open(log_path, "w"), out_dir, MersenneTwister(SEED))

    commit = strip(cmd_out(`git rev-parse --short HEAD`))
    t = now()
    println_loud(rs, "$(t) $(commit) $(join(ARGS, " "))")
    println_loud(rs, "== Config ==")
    println_loud(rs, "TAG: $(TAG)")
    println_loud(rs, generation_params)
    println_loud(rs, loss_params)
    println_loud(rs, "Epochs: $(epochs)")
    println_loud(rs, "Learning rate: $(learning_rate)")
    println_loud(rs, "DistNat: $(DistNat)")
    println_loud(rs, "SEED: $(SEED)")
    println_loud(rs)
    println("Logging to $(log_path)")
    println()

    mgr = create_benchmark_manager(rs, generation_params, loss_params)
    print_adnodes_of_interest(rs, "initial")
    mgr.emit_stats("initial")
    mgr.loss_mgr.train!(; epochs, learning_rate)
    print_adnodes_of_interest(rs, "trained")
    mgr.emit_stats("trained")
    t′ = now()

    println_loud(rs, t′)
    println_loud(rs, "Total time elapsed: $(canonicalize(t′ - t))")
    # include("dump_loss_graph.jl")
end
