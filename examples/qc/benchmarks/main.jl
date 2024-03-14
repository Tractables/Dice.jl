include("benchmarks.jl")


# GENERATION_PARAMS_LIST = [
#     TypeBasedRBTGenerator(size=5,color_by_size=true,learn_leaf_weights=false,use_parent_color=true),
#     TypeBasedRBTGenerator(size=5,color_by_size=true,learn_leaf_weights=false,use_parent_color=false),
# ]
# LR_LIST = [0.1, 0.3, 1, 3, 10, 30, 100, 300]
# LOSS_CONFIG_WEIGHT_PAIRS_LIST = collect(Iterators.flatten([
#     (
#         [
#             SamplingEntropy{RBT}(resampling_frequency=2, samples_per_batch=10000) => lr,
#         ]
#         for lr in LR_LIST
#     ),
# ]))
# EPOCHS_LIST = [100_000]

GENERATION_PARAMS_LIST = [Flips{3}()]
LR_LIST = [0.0001, 0.0003, 0.001, 0.003, 0.01, 0.03, 0.1, 0.3, 1, 3, 10, 30, 100, 300]
LOSS_CONFIG_WEIGHT_PAIRS_LIST = collect(Iterators.flatten([
    (
        [
            SamplingEntropy{Bools{3}}(resampling_frequency=1000, samples_per_batch=100) => lr,
        ]
        for lr in LR_LIST
    ),
]))
EPOCHS_LIST = [10000]

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

