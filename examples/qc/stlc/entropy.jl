# Train an STLC generator to have some property (term size or num apps) match a
# specific distribution (linear or uniform).
#
# Saves the distributions and sampled terms before and after training.

using Dice
include("lib/dist.jl")
include("lib/util.jl")
include("lib/generator.jl")

############################
# Config
############################

# Specify generator, initial & target distributions
METRIC = "entropy"
INIT_SIZE = 2      # size passed to top call of gen_expr
GEN_TYP_SIZE = 1   # size passed to all calls of gen_type

# Hyperparams
PARAMETERIZE_FLIP_GROUPS_BY_SZ = true  # whether flips at the same code location
                                       # but different sizes can have different
                                       # probabilities
EPOCHS = 2000  # epochs to train for

LOG_TO_FILE = true

TAG = "v3_opt_meta_ad"

############################

# Corresponds to "problem" - generator we are trying to train & desired dist.
# Data within a directory would get plotted on the same graph
OUT_DIR = "examples/qc/stlc/output/$(TAG)/$(METRIC)/sz=$(INIT_SIZE),tysz=$(GEN_TYP_SIZE)"

# Hyperparams
OUT_FILE_TAG = "param_by_sz=$(PARAMETERIZE_FLIP_GROUPS_BY_SZ),epochs=$(EPOCHS)"

############################
# Intro
############################

LOG_PATH = joinpath(OUT_DIR, "log_" * OUT_FILE_TAG * ".log")
LEARNING_CURVE_PATH = joinpath(OUT_DIR, "learning_curve_" * OUT_FILE_TAG * ".csv")

mkpath(OUT_DIR)
io = if LOG_TO_FILE
    open(LOG_PATH, "w")
else
    stdout
end

using Dates
t = now()
for io′ in Set([io, stdout])
    println(io′, t)
    println(io′, "== Config ==")
    println(io′, "INIT_SIZE: $(INIT_SIZE)")
    println(io′, "GEN_TYP_SIZE: $(GEN_TYP_SIZE)")
    println(io′, "PARAMETERIZE_FLIP_GROUPS_BY_SZ: $(PARAMETERIZE_FLIP_GROUPS_BY_SZ)")
    println(io′, "EPOCHS: $(EPOCHS)")
    println(io′, "DistNat: $(DistNat)")
    println(io′, "TAG: $(TAG)")
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
    var_vals[var] = 0
    weight = sigmoid(var)
    adnodes_of_interest[s] = weight
    weight
end

println_flush(io, "Building (gen_expr(...)) computation graph...")
time_build = @elapsed begin
    e = gen_expr(
        DistNil(DistI{Typ}),
        gen_type(GEN_TYP_SIZE, PARAMETERIZE_FLIP_GROUPS_BY_SZ),
        INIT_SIZE,
        GEN_TYP_SIZE,
        PARAMETERIZE_FLIP_GROUPS_BY_SZ
    )
end
println(io, "  $(time_build) seconds")
println(io)


############################
# Before
############################

println(io, "Initial adnodes_of_interest:")
vals = compute(var_vals, values(adnodes_of_interest))
show(io, Dict(s => vals[adnode] for (s, adnode) in adnodes_of_interest))
println(io)


println_flush(io, "Saving samples...")
time_sample_init = @elapsed with_concrete_ad_flips(var_vals, e) do
    save_samples(joinpath(OUT_DIR, "terms_before.txt"), e; io=io)
end
println(io, "  $(time_sample_init) seconds")
println(io)

to_id = Dict(
    "Var" => DistUInt32(1),
    "Boolean" => DistUInt32(2),
    "App" => DistUInt32(3),
    "Abs" => DistUInt32(4),
)

function collect_terminals(e)
    match(e, [
        "Var"     => (i)        -> DistVector([to_id["Var"]]),
        "Boolean" => (b)        -> DistVector([to_id["Boolean"]]),
        "App"     => (f, x)    -> prob_append(prob_extend(collect_terminals(f), collect_terminals(x)), to_id["App"]),
        "Abs"     => (ty, e′)  -> prob_append(collect_terminals(e′), to_id["Abs"]),
    ])
end
random_term = match(e, [
    "None" => () -> DistNone(DistUInt32),
    "Some" => e -> DistSome(choice(collect_terminals(e)))
])
loss = neg_entropy(random_term, Set([DistSome(i) for i in values(to_id)]))

initial_entropy = compute_mixed(var_vals, -loss)
println(io, "Initial entropy: $(initial_entropy)")
println(io)

############################
# Train
############################

println_flush(io, "Training...")
time_train = @elapsed learning_curve = train!(var_vals, loss; epochs=EPOCHS, learning_rate=0.003)
println(io, "  $(time_train) seconds")
println(io)

open(LEARNING_CURVE_PATH, "w") do file
    for (epoch, logpr) in zip(0:EPOCHS, learning_curve)
        println(file, "$(epoch)\t$(logpr)")
    end
end

############################
# After
############################

final_entropy = compute_mixed(var_vals, -loss)
println(io, "Final entropy: $(final_entropy)")
println(io)

println(io, "Learned adnodes_of_interest:")
vals = compute(var_vals, values(adnodes_of_interest))
show(io, Dict(s => vals[adnode] for (s, adnode) in adnodes_of_interest))
println(io)

println(io, "Saving samples...")
time_sample_final = @elapsed with_concrete_ad_flips(var_vals, e) do
    save_samples(joinpath(OUT_DIR, "terms_trained_" * OUT_FILE_TAG * ".txt"), e; io=io)
end
println(io, "  $(time_sample_final) seconds")
println(io)
