using Revise
using Dice
using Random

# Finding accuracy errors in an approximate inverse square root function

# Current output of this program (nondeterministic):
# 15.127460 seconds (141.17 M allocations: 6.819 GiB, 6.44% gc time, 19.28% compilation time)
# Initial p(bugfound) = 0.011
# Trained p(bugfound) = 0.99

################################################################################
# HYPERPARAMETERS AND CONFIG
################################################################################

# How many steps of Newton's method to take. Increase to make the approximate fn
# more accurate
STEPS = 5

# Precision of the fixed point number generator. Increase to be able to generate
# numbers closer to 0
PREC=10

# We consider a bug to be found if we get relative error BUG_THRESH
# Note: relative error is from approx_inv_sqrt(x)^2 to 1/x. This prevents us
# from needing a preexisting implementation of sqrt.
# Maybe this helps the story, but it also makes "relative error" a bit harder to
# explain so maybe we should just use `sqrt`, and measure error from
# approx_inv_sqrt(x) to 1/sqrt(x).
BUG_THRESH = 0.01

# Training
NUM_EPOCHS = 100
NUM_SAMPLES = 1000
LR = 0.03

################################################################################
# DistZeroToOne
################################################################################

# Probabilistic value from zero to one. TODO: use DistFix
import Dice: tobits, frombits, prob_equals
struct DistZeroToOne <: Dist{Any}
    mantissa::DistUInt
end
tobits(x::DistZeroToOne) = tobits(x.mantissa)
frombits(x::DistZeroToOne, world) =
    float(frombits(x.mantissa, world)) / 2^float(length(x.mantissa.bits))
DistZeroToOne(x::Float64, W) = DistZeroToOne(DistUInt{W}(Int(x * 2^W)))
prob_equals(x::DistZeroToOne, y::DistZeroToOne) =
    prob_equals(x.mantissa, y.mantissa)


################################################################################
# Approximate inverse square root and its error
################################################################################

# Thanks to REINFORCE, none of these functions need be implemented in Dice

# Approximate sqrt(x) by Newton's method
function approx_sqrt(x, steps)
    guess = 1
    for _ in 1:steps
        guess = 1/2 * (guess + x/guess)
    end
    guess
end

approx_inv_sqrt(x, steps) = 1/approx_sqrt(x, steps)

rel_error(actual, expected) = abs((actual - expected) / expected)

# Note we don't need an "oracle" (an existing `sqrt`` function) to target error!
# We instead compare the squared approx-inverse-sqrt to the inverse.
# Maybe this helps the story, but it also makes "relative error" a bit harder to
# explain so maybe we should just use `sqrt`.
approx_inv_sqrt_error(x, steps) = rel_error(approx_inv_sqrt(x, steps)^2, 1/x)

################################################################################
# Generator
################################################################################

var_vals = Valuation()
adnodes_of_interest = Dict{String, ADNode}()
function register_weight!(s)
    var = Var("$(s)_before_sigmoid")
    var_vals[var] = 0
    weight = sigmoid(var)
    adnodes_of_interest[s] = weight
    weight
end

# Uniform from 0 to 1
g = DistZeroToOne(DistUInt{PREC}([
    flip(register_weight!("x_$(i)"))
    for i in 1:PREC
]))

################################################################################
# Train to maximize error
################################################################################

history_err = []
history_p_bugfound = []

@time for epoch in 1:NUM_EPOCHS
    samples = Dice.with_concrete_ad_flips(var_vals, g) do
      [sample(Random.default_rng(), g) for _ in 1:NUM_SAMPLES]
    end

    l = Dice.LogPrExpander(WMC(BDDCompiler([
        prob_equals(g, DistZeroToOne(sample, PREC))
        for sample in samples
    ])))
    loss, total_dist, valid_samples, samples_finding_bug = sum(
        begin
            lpr_eq = Dice.expand_logprs(l, LogPr(prob_equals(g, DistZeroToOne(sample, PREC))))
            dist = approx_inv_sqrt_error(sample, STEPS)
            if isnan(dist)
                [Dice.Constant(0), 0, 0, 0]
            else
                [-lpr_eq * dist, dist, 1, if dist > BUG_THRESH 1 else 0 end]
            end
        end
        for sample in samples
    )
    push!(history_err, total_dist / valid_samples)
    push!(history_p_bugfound, samples_finding_bug / NUM_SAMPLES)

    vals, derivs = differentiate(
        var_vals,
        Derivs(loss => 1)
    )
    for (adnode, d) in derivs
        if adnode isa Var
            var_vals[adnode] -= d * LR
        end
    end
end

println("Initial p(bugfound) = $(first(history_p_bugfound))")
println("Trained p(bugfound) = $(last(history_p_bugfound))")
