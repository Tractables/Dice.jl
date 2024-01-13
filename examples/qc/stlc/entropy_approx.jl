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

TAG = "entropy_approx_v01"

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

function ctor_to_id(ctor)
    match(ctor, [
        "Var" => _ -> DistInt32(0)
        "Boolean" => _ -> DistInt32(1)
        "App" => (_, _) -> DistInt32(2)
        "Abs" => (_, _) -> DistInt32(3)
    ])
end

function opt_ctor_to_id(opt_ctor)
    match(opt_ctor, [
        "Some" => ctor_to_id,
        "None" => () -> DistInt32(-1),
    ])
end

generated_constructors = DistInt32[]
function add_ctor(v::DistI{Opt{DistI{Expr}}})
    push!(generated_constructors, opt_ctor_to_id(v))
    v
end


println_flush(io, "Building (gen_expr(...)) computation graph...")
generated_constructors = []
time_build = @elapsed begin
    e = gen_expr(
        DistNil(DistI{Typ}),
        gen_type(GEN_TYP_SIZE, PARAMETERIZE_FLIP_GROUPS_BY_SZ),
        INIT_SIZE,
        GEN_TYP_SIZE,
        PARAMETERIZE_FLIP_GROUPS_BY_SZ,
        add_ctor
    )
end
println(io, "  $(time_build) seconds")
println(io)

ctor = generated_constructors[2]
function neg_entropy2(p::Dist, domain::Set{<:Dist})
    sum(domain) do x
        pe = prob_equals(p, x)
        if length(support_mixed(pe)) == 1
            Dice.Constant(0)
        else
            LogPr(pe) * exp(LogPr(pe))
        end
    end
end
generated_constructors
# compute_mixed(neg_entropy2())
compute_mixed(var_vals, LogPr(prob_equals(generated_constructors[end], DistInt32(0))))
[compute_mixed(var_vals, neg_entropy2(ctor, Set([DistInt32(i) for i in 0:3]))) for ctor in generated_constructors]
prob_equals(ctor, DistInt32(2))

loss = sum(
    neg_entropy2(ctor, Set([DistInt32(i) for i in 0:3]))
    for ctor in generated_constructors
    if begin
        sup = support_mixed(ctor)
        ct = sum(1 for i in 0:3 if i in sup)
        ct > 1
    end
)
compute_mixed(var_vals, loss)

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


initial_entropy = compute_mixed(var_vals, -loss)
println(io, "Initial entropy: $(initial_entropy)")
println(io)

############################
# Train
############################

println_flush(io, "Training...")
time_train = @elapsed learning_curve = train!(var_vals, loss; epochs=EPOCHS, learning_rate=0.03)
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
