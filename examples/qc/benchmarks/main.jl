include("benchmarks.jl")


GENERATION_PARAMS_LIST = [
    BespokeSTLCGenerator(param_vars_by_size=true,size=5,ty_size=2),
    # BespokeBSTGenerator(size=5, vals=BSTDummyVals),
    # TypeBasedBSTGenerator(size=5),
]
LR_LIST = [0.001, 0.003, 0.01, 0.03, 0.1, 0.3, 1, 3, 10]
LOSS_CONFIG_WEIGHT_PAIRS_LIST = collect(Iterators.flatten([
    (
        [
            SamplingEntropy{STLC}(resampling_frequency=2, samples_per_batch=1_000) => lr,
        ]
        for lr in LR_LIST
    ),
]))
EPOCHS_LIST = [10_000]

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
    err = IOBuffer()
    @async begin
        proc = run(pipeline(cmd; stdout=out, stderr=err),)
        if proc.exitcode != 0
            println()
            so = String(take!(out))
            se = String(take!(err))
            println("FAILED: $(s)\nSTDOUT ===\n$(so)\nSTDERR ===\n$(se)\n")
        else
            se = String(take!(err))
            println(se)
        end
    end
end

