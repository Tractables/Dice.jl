using Dice
include("lib/dist.jl")
include("lib/util.jl")
include("lib/generator.jl")

############################
# Config
############################

METRIC = term_size  # term_size or num_apps
INIT_SIZE = 3
GEN_TYP_SIZE = 2
OUT_PATH_PREFIX = "$(METRIC)_sz$(INIT_SIZE)_tysz$(GEN_TYP_SIZE)"

############################
# Intro
############################

println("== Config ==")
@show INIT_SIZE
@show GEN_TYP_SIZE
@show DistNat
println()

println("Building $(METRIC)(gen_expr(...)) computation graph...")
@time begin
    e = gen_expr(DistNil(DistI{Typ}), gen_type(GEN_TYP_SIZE), DistNat(INIT_SIZE), GEN_TYP_SIZE)
    metric = METRIC(e)
end
println()


############################
# Before
############################

println("Initial group probs:")
display(get_group_probs())
println()

println("Inferring initial distribution...")
@time metric_dist = pr(metric)
save_metric_dist("$(OUT_PATH_PREFIX)_before.csv", METRIC, metric_dist)
println()

save_samples("$(OUT_PATH_PREFIX)_terms_before.txt", e)
println("Saved samples to $(OUT_PATH_PREFIX)_terms_before.txt")
println()


############################
# Train
############################

println("Training...")
bools_to_max = [prob_equals(metric, DistUInt32(i)) for i in key_range(metric_dist)]
@time train_group_probs!(bools_to_max)
println()


############################
# After
############################

println("Learned group probs:")
display(get_group_probs())
println()

println("Inferring trained distribution...")
@time metric_dist_after = pr(metric)
save_metric_dist("$(OUT_PATH_PREFIX)_after.csv", METRIC, metric_dist_after)
println()

save_samples("$(OUT_PATH_PREFIX)_terms_after.txt", e)
println("Saved samples to $(OUT_PATH_PREFIX)_terms_after.txt")
println()

