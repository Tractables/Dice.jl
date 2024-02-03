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

generation_params = STLCGenerationParams(
    param_vars_by_size=true,
    size=3,
    ty_size=2,
)
loss_params = MixedLossParams(Pair{SimpleLossParams{STLC}, Real}[
    ApproxSTLCConstructorEntropy() => 10,
    MLELossParams(
        metric=NumApps(),
        target_dist=Target4321(),
    ) => 1,
])


# generation_params = BSTGenerationParams(size=3)
# loss_params = ApproxBSTConstructorEntropy()

EPOCHS = 500
LEARNING_RATE = if loss_params isa ApproxSTLCConstructorEntropy 0.03 else 0.01 end

TAG = "v05"

LOG_TO_FILE = true

############################

path = joinpath(
    vcat(
        [TAG],
        to_subpath(generation_params),
        to_subpath(loss_params),
        ["epochs=$(EPOCHS),learning_rate=$(LEARNING_RATE)"],
    )
)
OUT_DIR = "examples/qc/benchmarks/output/$(path)"

###########################

LOG_PATH = joinpath(OUT_DIR, "log.log")

mkpath(OUT_DIR)
io = if LOG_TO_FILE open(LOG_PATH, "w") else stdout end

using Dates
t = now()
for io′ in Set([io, stdout])
    println(io′, t)
    println(io′, "== Config ==")
    println(io′, "TAG: $(TAG)")
    println(io′, generation_params)
    println(io′, loss_params)
    println(io′, "EPOCHS: $(EPOCHS)")
    println(io′, "LEARNING_RATE: $(LEARNING_RATE)")
    println(io′, "DistNat: $(DistNat)")
    println(io′)
end
if LOG_TO_FILE
    println("Logging to $(LOG_PATH)")
    println()
end

var_vals = Valuation()
adnodes_of_interest = Dict{String, ADNode}()
function register_weight!(s)
    var = Var("$(s)_before_sigmoid")
    if !haskey(var_vals, var) || var_vals[var] == 0
        var_vals[var] = 0
    else
        println(io, "WARNING: not registering fresh weight for $(s)")
    end
    weight = sigmoid(var)
    adnodes_of_interest[s] = weight
    weight
end


println_flush(io, "Initial adnodes_of_interest:")
vals = compute(var_vals, values(adnodes_of_interest))
showln(io, Dict(s => vals[adnode] for (s, adnode) in adnodes_of_interest))

mgr = create_benchmark_manager(io, OUT_DIR, var_vals, generation_params, loss_params)
mgr.emit_stats("initial")
mgr.train!(epochs=EPOCHS, learning_rate=LEARNING_RATE)


println(io, "Trained adnodes_of_interest:")
vals = compute(var_vals, values(adnodes_of_interest))
showln(io, Dict(s => vals[adnode] for (s, adnode) in adnodes_of_interest))

mgr.emit_stats("trained")
