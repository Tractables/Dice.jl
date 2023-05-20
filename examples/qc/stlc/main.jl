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
PARAMETERIZE_FLIP_GROUPS_BY_SZ = true
LINEAR = false  # by default, the desired distribution is uniform. 

############################

dist_desc = if LINEAR "linear" else "uniform" end
OUT_DIR = "examples/qc/stlc/output/$(METRIC)/$(dist_desc)/sz=$(INIT_SIZE),tysz=$(GEN_TYP_SIZE)"
OUT_PREFIX = "param_by_sz=$(PARAMETERIZE_FLIP_GROUPS_BY_SZ)"

############################
# Intro
############################

mkpath(OUT_DIR)

println("== Config ==")
@show INIT_SIZE
@show GEN_TYP_SIZE
@show PARAMETERIZE_FLIP_GROUPS_BY_SZ
@show DistNat
flush_println()

println("Building $(METRIC)(gen_expr(...)) computation graph...")
@time begin
    e = gen_expr(
        DistNil(DistI{Typ}),
        gen_type(GEN_TYP_SIZE, PARAMETERIZE_FLIP_GROUPS_BY_SZ),
        INIT_SIZE,
        GEN_TYP_SIZE,
        PARAMETERIZE_FLIP_GROUPS_BY_SZ
    )
    metric = METRIC(e)
end
flush_println()


############################
# Before
############################

println("Initial group probs:")
display(get_group_probs())
flush_println()

println("Inferring initial distribution...")
@time metric_dist = pr(metric)
save_metric_dist(joinpath(OUT_DIR, OUT_PREFIX * "_before.csv"), METRIC, metric_dist)
flush_println()

println("Saving samples...")
save_samples(joinpath(OUT_DIR, OUT_PREFIX * "_terms_before.txt"), e)
flush_println()


############################
# Train
############################

println("Training...")
bools_to_max = [
    BoolToMax(prob_equals(metric, DistUInt32(i)), weight=if LINEAR i else 1 end)
    for i in key_range(metric_dist)
]
@time train_group_probs!(bools_to_max)
flush_println()


############################
# After
############################

println("Learned group probs:")
display(get_group_probs())
flush_println()

println("Inferring trained distribution...")
@time metric_dist_after = pr(metric)
save_metric_dist(joinpath(OUT_DIR, OUT_PREFIX * "_after.csv"), METRIC, metric_dist_after)
flush_println()

println("Saving samples...")
save_samples(joinpath(OUT_DIR, OUT_PREFIX * "_terms_after.txt"), e)
flush_println()
