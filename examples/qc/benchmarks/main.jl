include("benchmarks.jl")

GENERATION_PARAMS_LIST = [
    TypeBasedSTLCGenerator(
        size=5,
        ty_size=2,
        dependents=[:size,:last_callsite],
        ty_dependents=[:size,:last_callsite],
    )
    # TypeBasedRBTGenerator(
    #     size=5,
    #     leaf_dependents=[:size,:parent_color,:last_callsite],
    #     red_dependents=[:size,:parent_color,:last_callsite],
    #     num_dependents=[:size,:parent_color,:last_callsite],
    #     intwidth=6,
    # ),
]
LR_LIST = [0.0003, 0.001, 0.003, 0.01, 0.03, 0.1, 0.3, 1., 3.]
FP_LIST = [0.]
RESAMPLING_FREQUENCY_LIST = [2]
SAMPLES_PER_BATCH_LIST = [200]
EPOCHS_LIST = [2000]
IGNORE_NUMS_LIST = [true]

n_runs = prod(map(length, [GENERATION_PARAMS_LIST, LR_LIST, FP_LIST, RESAMPLING_FREQUENCY_LIST, SAMPLES_PER_BATCH_LIST, EPOCHS_LIST, IGNORE_NUMS_LIST]))
println(n_runs)
@assert n_runs <= 36

@show GENERATION_PARAMS_LIST
@show LR_LIST
@show FP_LIST
@show RESAMPLING_FREQUENCY_LIST
@show SAMPLES_PER_BATCH_LIST
@show EPOCHS_LIST
@show IGNORE_NUMS_LIST
println()

LOSS_CONFIG_WEIGHT_PAIRS_LIST = collect(Iterators.flatten([
    (
        [
            SamplingEntropy{STLC}(
                resampling_frequency=resampling_frequency,
                samples_per_batch=samples_per_batch,
                property=STLCWellTyped(),
                failure_penalty=fp,
                ignore_nums=ignore_nums,
            ) => lr,
            # SamplingEntropy{RBT}(
            #     resampling_frequency=resampling_frequency,
            #     samples_per_batch=samples_per_batch,
            #     property=MultipleInvariants([
            #         BookkeepingInvariant(),
            #         BalanceInvariant(),
            #         OrderInvariant(),
            #     ]),
            #     failure_penalty=fp,
            #     ignore_nums=ignore_nums,
            # ) => 0.01,
            # MLELossConfig(RBTDepth(), Uniform()) => lr,
            # SatisfyPropertyLoss(MultipleInvariants([BookkeepingInvariant(),BalanceInvariant()])) => lr,
        ]
        for lr in LR_LIST
        for fp in FP_LIST
        for resampling_frequency in RESAMPLING_FREQUENCY_LIST
        for samples_per_batch in SAMPLES_PER_BATCH_LIST
        for ignore_nums in IGNORE_NUMS_LIST
    ),
]))


# N = 4
# GENERATION_PARAMS_LIST = [Flips{N}()]
# # LR_LIST = [0.0001, 0.0003, 0.001, 0.003, 0.01, 0.03, 0.1, 0.3, 1, 3, 10, 30, 100, 300]
# LR_LIST = [0.0001, 0.0002, 0.0005, 0.001, 0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1, 3, 10, 30, 100]
# LOSS_CONFIG_WEIGHT_PAIRS_LIST = collect(Iterators.flatten([
#     (
#         [
#             # BoolsExactEntropy{3}() => lr,
#             SamplingEntropy{Bools{N}}(resampling_frequency=10, samples_per_batch=100) => lr,
#         ]
#         for lr in LR_LIST
#     ),
# ]))
# EPOCHS_LIST = [10_000]

TOOL_PATH = "examples/qc/benchmarks/tool.jl"

@sync for (p, lcws, epochs) in Base.product(GENERATION_PARAMS_LIST, LOSS_CONFIG_WEIGHT_PAIRS_LIST, EPOCHS_LIST)
    flags = join([s for s in ARGS if startswith(s, "-")], " ")
    lcws_s = replace(string(lcws), " "=>"")
    p_s = replace(string(p), " "=>"")
    s = "julia --project $(TOOL_PATH) $(flags) $(p_s) $(lcws_s) $(epochs)"
    cmd = Cmd(Cmd(convert(Vector{String}, split(s))), ignorestatus=true)
    println(s)
    out = IOBuffer()
    @async begin
        proc = run(pipeline(cmd; stdout=out, stderr=stdout),)
        if proc.exitcode != 0
            println()
            so = String(take!(out))
            println("FAILED: $(s)\nSTDOUT ===\n$(so)\n\n")
        end
    end
end

