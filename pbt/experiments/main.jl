include("benchmarks.jl")

GENERATION_PARAMS_LIST = [
    # LangBespokeSTLCGenerator(
    #     expr_size=5,
    #     typ_size=2,
    # ),
    # LangSiblingDerivedGenerator{STLC}(
    #     root_ty=Expr.t,
    #     ty_sizes=[Expr.t=>5, Typ.t=>2],
    #     stack_size=2,
    #     intwidth=3,
    # )
    # LangSiblingDerivedGenerator{RBT}(
    #     root_ty=ColorKVTree.t,
    #     ty_sizes=[ColorKVTree.t=>4, Color.t=>0],
    #     stack_size=2,
    #     intwidth=3,
    # ),
#    LangSiblingDerivedGenerator{BST}(
#        root_ty=KVTree.t,
#        ty_sizes=[KVTree.t=>4],
#        stack_size=2,
#        intwidth=3,
#    ),

#    LangDerivedGenerator{STLC}(
#        root_ty=Expr.t,
#        ty_sizes=[Expr.t=>5, Typ.t=>2],
#        arbitrary_prims=true,
#        stack_size=0,
#        intwidth=3,
#    ),
   LangDerivedGenerator{RBT}(
       root_ty=ColorKVTree.t,
       ty_sizes=[ColorKVTree.t=>4, Color.t=>0],
    #    arbitrary_prims=true,
       arbitrary_prims=false,
       stack_size=0,
       intwidth=3,
   ),
#    LangDerivedGenerator{BST}(
#        root_ty=KVTree.t,
#        ty_sizes=[KVTree.t=>4],
#        arbitrary_prims=true,
#        stack_size=0,
#        intwidth=3,
#    ),
]
# LR_LIST = [0.3]
LR_LIST = [0.03, 0.1, 0.3, 1.0]

# SAMPLES_PER_BATCH_LIST = [200]
# SAMPLES_PER_BATCH_LIST = [2000]
# RESAMPLING_FREQUENCY_LIST = [1]
EPOCHS_LIST = [2] #, 10000]

SAMPLES_PER_BATCH_LIST = [200]
# SAMPLES_PER_BATCH_LIST = [2000]
RESAMPLING_FREQUENCY_LIST = [2]
EPOCHS_LIST = [1000]
BOUND_LIST = [0.1]

# SAMPLES_PER_BATCH_LIST = [nothing]
# PROPERTY_LIST = [nothing]

PROPERTY_LIST = [isRBT]

# TRAIN_FEATURE_LIST = [false, true]
TRAIN_FEATURE_LIST = [true]

n_runs = prod(map(length, [GENERATION_PARAMS_LIST, LR_LIST, PROPERTY_LIST, RESAMPLING_FREQUENCY_LIST, SAMPLES_PER_BATCH_LIST, EPOCHS_LIST, BOUND_LIST, TRAIN_FEATURE_LIST]))
println(n_runs)
@assert n_runs <= 12

@show GENERATION_PARAMS_LIST
@show LR_LIST
@show PROPERTY_LIST
@show RESAMPLING_FREQUENCY_LIST
@show SAMPLES_PER_BATCH_LIST
@show EPOCHS_LIST
@show BOUND_LIST
println()


function workload_of(::Type{<:GenerationParams{T}}) where T
    T
end
wl = workload_of(typeof(GENERATION_PARAMS_LIST[1]))

LOSS_CONFIG_WEIGHT_PAIRS_LIST = []
# append!(LOSS_CONFIG_WEIGHT_PAIRS_LIST,
#     (
#         # [SpecEntropy{RBT}(resampling_frequency,samples_per_batch,property) => lr]
#         [MLELossConfig{wl}(depth, target) => lr]
#         for lr in LR_LIST
#         for property in PROPERTY_LIST
#         for resampling_frequency in RESAMPLING_FREQUENCY_LIST
#         for samples_per_batch in SAMPLES_PER_BATCH_LIST
#         for target in [Uniform(), Linear()]
#     )
# )

append!(LOSS_CONFIG_WEIGHT_PAIRS_LIST,
    (
        [SpecEntropy{RBT}(resampling_frequency,samples_per_batch,property) => lr]
        for lr in LR_LIST
        for property in PROPERTY_LIST
        for resampling_frequency in RESAMPLING_FREQUENCY_LIST
        for samples_per_batch in SAMPLES_PER_BATCH_LIST
    ),
)
# append!(LOSS_CONFIG_WEIGHT_PAIRS_LIST,
#     (
#         [SatisfyPropertyLoss{RBT}(isRBTdist) => lr]
#         for lr in LR_LIST
#     ),
# )

# LOSS_CONFIG_WEIGHT_PAIRS_LIST = []
# append!(LOSS_CONFIG_WEIGHT_PAIRS_LIST,
#     (
#         [MLELossConfig{STLC}(size, Target4321()) => lr]
#         for lr in LR_LIST
#         for property in PROPERTY_LIST
#         for resampling_frequency in RESAMPLING_FREQUENCY_LIST
#         for samples_per_batch in SAMPLES_PER_BATCH_LIST
#     ),
# )
# append!(LOSS_CONFIG_WEIGHT_PAIRS_LIST,
#     (
#         [MLELossConfig{STLC}(num_apps, Target333()) => lr]
#         for lr in LR_LIST
#         for property in PROPERTY_LIST
#         for resampling_frequency in RESAMPLING_FREQUENCY_LIST
#         for samples_per_batch in SAMPLES_PER_BATCH_LIST
#     ),
# )

# LOSS_CONFIG_WEIGHT_PAIRS_LIST = begin
#     lr = 0.03
#     function workload_of(::Type{<:GenerationParams{T}}) where T
#         T
#     end
#     wl = workload_of(typeof(GENERATION_PARAMS_LIST[1]))
#     [
#         [MLELossConfig{wl}(depth, Linear()) => lr],
#         [MLELossConfig{wl}(depth, Uniform()) => lr],
#         [MLELossConfig{wl}(size, Linear()) => lr],
#         [MLELossConfig{wl}(size, Uniform()) => lr],
#     ]
# end

# N = 3
# GENERATION_PARAMS_LIST = [Flips{N}()]
# LR_LIST = [0.0001, 0.0003, 0.001, 0.003, 0.01, 0.03, 0.1, 0.3, 1, 3, 10, 30, 100, 300]
# LR_LIST = [0.0001, 0.0002, 0.0005, 0.001, 0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1, 3, 10, 30, 100]
# LOSS_CONFIG_WEIGHT_PAIRS_LIST = collect(Iterators.flatten([
#     (
#         [
#             # BoolsExactEntropy{3}() => lr,
#             SamplingEntropy{Bools{N}}(
#                 resampling_frequency=1,
#                 samples_per_batch=300,
#                 property=TrueProperty{Bools{N}}(),
#                 eq=:prob_equals,
#                 failure_penalty=0.,
#                 forgiveness=0,
#                 rand_forgiveness=true,
#                 keyf=:identity,
#             ) => lr,
#         ]
#         for lr in LR_LIST
#     ),
# ]))
# EPOCHS_LIST = [100]

TOOL_PATH = "qc/benchmarks/tool.jl"

@sync for (p, lcws, epochs, bound) in Base.product(GENERATION_PARAMS_LIST, LOSS_CONFIG_WEIGHT_PAIRS_LIST, EPOCHS_LIST, BOUND_LIST)
    flags = join([s for s in ARGS if startswith(s, "-")], " ")
    lcws_s = replace(string(lcws), " "=>"")
    p_s = replace(string(p), " "=>"")
    s = "julia --project $(TOOL_PATH) $(flags) $(p_s) $(lcws_s) $(epochs) $(bound)"
    cmd = Cmd(Cmd(convert(Vector{String}, split(s))), ignorestatus=true)
    s_hum = "julia --project $(TOOL_PATH) $(flags) \"$(p_s)\" \"$(lcws_s)\" $(epochs) $(bound)"
    println(s_hum)
    out = IOBuffer()
    @async begin
        proc = run(pipeline(cmd; stdout=out, stderr=stdout),)
        if proc.exitcode != 0
            println()
            println(proc.exitcode)
            so = String(take!(out))
            println("FAILED:\n$(s_hum)\nSTDOUT ===\n$(so)\n\n")
        end
    end
end

