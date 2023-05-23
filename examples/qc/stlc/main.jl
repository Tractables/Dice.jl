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

METRIC = num_apps  # term_size or num_apps
INIT_SIZE = 3
GEN_TYP_SIZE = 2
LINEAR = false  # by default, the desired distribution is uniform.

PARAMETERIZE_FLIP_GROUPS_BY_SZ = true
EPOCHS = 4000

LOG_TO_FILE = true

############################

dist_desc = if LINEAR "linear" else "uniform" end

# Corresponds to "problem" - generator we are trying to train & desired dist.
# Data within a directory would get plotted on the same graph
OUT_DIR = "examples/qc/stlc/output/$(METRIC)/$(dist_desc)/sz=$(INIT_SIZE),tysz=$(GEN_TYP_SIZE)"

# Hyperparams
OUT_FILE_TAG = "param_by_sz=$(PARAMETERIZE_FLIP_GROUPS_BY_SZ),epochs=$(EPOCHS)"

############################
# Intro
############################

LOG_PATH = joinpath(OUT_DIR, "log_" * OUT_FILE_TAG * ".log")

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
    println(io′)
end
if LOG_TO_FILE
    println("Logging to $(LOG_PATH)")
    println()
end

println_flush(io, "Building $(METRIC)(gen_expr(...)) computation graph...")
time_build = @elapsed begin
    e = gen_expr(
        DistNil(DistI{Typ}),
        gen_type(GEN_TYP_SIZE, PARAMETERIZE_FLIP_GROUPS_BY_SZ),
        INIT_SIZE,
        GEN_TYP_SIZE,
        PARAMETERIZE_FLIP_GROUPS_BY_SZ
    )
    metric = METRIC(e)
end
println(io, "  $(time_build) seconds")
println(io)


############################
# Before
############################

println(io, "Initial group probs:")
show(io, get_group_probs())
println(io)

println_flush(io, "Inferring initial distribution...")
time_infer_init = @elapsed metric_dist = pr(metric)
println(io, "  $(time_infer_init) seconds")
save_metric_dist(joinpath(OUT_DIR, "dist_before.csv"), METRIC, metric_dist; io=io)
println(io)

println_flush(io, "Saving samples...")
time_sample_init = @elapsed save_samples(joinpath(OUT_DIR, "terms_before.txt"), e; io=io)
println(io, "  $(time_sample_init) seconds")
println(io)

bools_to_max = [
    BoolToMax(prob_equals(metric, DistUInt32(i)), weight=if LINEAR i else 1 end)
    for i in key_range(metric_dist)
]

initial_logprob = total_logprob(bools_to_max)
println(io, "Initial logprob: $(initial_logprob)")
println(io)

############################
# Train
############################

println_flush(io, "Training...")
time_train = @elapsed train_group_probs!(bools_to_max, EPOCHS)
println(io, "  $(time_train) seconds")
println(io)


############################
# After
############################

final_logprob = total_logprob(bools_to_max)
println(io, "Final logprob: $(final_logprob)")
approx_improvement = round(exp(final_logprob - initial_logprob), digits=2)
println(io, "Drawing the target dataset is $(approx_improvement)x more likely")
println(io)

println(io, "Learned group probs:")
show(io, get_group_probs())
println(io)

println(io, "Inferring trained distribution...")
time_infer_final = @elapsed metric_dist_after = pr(metric)
save_metric_dist(joinpath(OUT_DIR, "dist_trained_" * OUT_FILE_TAG * ".csv"), METRIC, metric_dist_after; io=io)
println(io)

println(io, "Saving samples...")
time_sample_final = @elapsed save_samples(joinpath(OUT_DIR, "terms_trained_" * OUT_FILE_TAG * ".txt"), e; io=io)
println(io, "  $(time_sample_final) seconds")
println(io)
