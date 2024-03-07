# Train an STLC generator to have some property (term size or num apps) match a
# specific distribution (linear or uniform).
#
# Saves the distributions and sampled terms before and after training.

using Dice
include("lib/lib.jl")
include("benchmarks.jl")

############################
# Config
############################

# loss_params = SamplingRBTEntropy(
#     resampling_frequency=2,
#     samples_per_batch=10000,
#     additional_loss_params=NullLoss{RBT}(),
#     # additional_loss_params=SatisfyPropertyLoss(MultipleInvariants([
#     #     BookkeepingInvariant(),
#     #     BalanceInvariant(),
#     #     BlackRootInvariant(),
#     # ])),
#     additional_loss_lr=0
# )
# loss_params = SatisfyPropertyLoss(BookkeepingInvariant())
EPOCHS=10000

var_vals = Valuation()
adnodes_of_interest = Dict{String, ADNode}()
function register_weight!(s)
    var = Var("$(s)_before_sigmoid")
    if !haskey(var_vals, var) || var_vals[var] == 0
        var_vals[var] = 0
    else
        println(io, "WARNING: not registering fresh weight for $(s)")
    end
    # var_vals[var] = inverse_sigmoid(rand())
    weight = sigmoid(var)
    adnodes_of_interest[s] = weight
    weight
end

for (generation_params, learning_rate) in Base.product(
    [
        TypeBasedRBTGenerator(size=5, color_by_size=true, learn_leaf_weights=true),
        TypeBasedRBTGenerator(size=5, color_by_size=true, learn_leaf_weights=false),
    ],
    [0.001, 0.003, 0.01, 0.03, 0.1, 0.3, 1.],
)
    empty!(var_vals)
    empty!(adnodes_of_interest)

    loss_params=SatisfyPropertyLoss(MultipleInvariants([
        BookkeepingInvariant(),
        BalanceInvariant(),
    ]))

    TAG = "v9_unif2"

    LOG_TO_FILE = true

    ############################

    path = joinpath(
        vcat(
            [TAG],
            to_subpath(generation_params),
            to_subpath(loss_params),
            ["epochs=$(EPOCHS)-learning_rate=$(learning_rate)"],
        )
    )
    OUT_DIR = "examples/qc/benchmarks/output/$(path)"

    ###########################

    LOG_PATH = joinpath(OUT_DIR, "log.log")

    if isfile(LOG_PATH) && "-f" ∉ ARGS
        println("Error: Log already exists at the following path:")
        println(LOG_PATH)
        println()
        continue
    end

    mkpath(OUT_DIR)
    io = if LOG_TO_FILE open(LOG_PATH, "w") else stdout end

    using Dates
    t = now()
    commit = strip(cmd_out(`git rev-parse --short HEAD`))
    for io′ in Set([io, stdout])
        println(io′, "$(t) $(commit) $(join(ARGS, " "))")
        println(io′, "== Config ==")
        println(io′, "TAG: $(TAG)")
        println(io′, generation_params)
        println(io′, loss_params)
        println(io′, "EPOCHS: $(EPOCHS)")
        println(io′, "LEARNING_RATE: $(learning_rate)")
        println(io′, "DistNat: $(DistNat)")
        println(io′)
    end
    if LOG_TO_FILE
        println("Logging to $(LOG_PATH)")
        println()
    end

    mgr = create_benchmark_manager(io, OUT_DIR, var_vals, generation_params, loss_params)

    println_flush(io, "ADNodes of interest (initial):")
    vals = compute(var_vals, values(adnodes_of_interest))
    showln(io, Dict(s => vals[adnode] for (s, adnode) in adnodes_of_interest))

    mgr.emit_stats("initial")
    mgr.loss_mgr.train!(; epochs=EPOCHS, learning_rate)


    println_flush(io, "ADNodes of interest (trained):")
    vals = compute(var_vals, values(adnodes_of_interest))
    showln(io, Dict(s => vals[adnode] for (s, adnode) in adnodes_of_interest))

    mgr.emit_stats("trained")

    t′ = now()
    println(io, t′)
    println(io, "Total time elapsed: $(canonicalize(t′ - t))")

    # include("dump_loss_graph.jl")
end