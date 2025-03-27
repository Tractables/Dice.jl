# An introduction to using MLE to learn flip probabilities

# Setup testing
using Test
using Alea
@testset "tour_2_learning" begin

################################################################################
# Maximizing expression probabilities
################################################################################

# What value of θ maximizes `pr(flip(θ) & flip(θ) & !flip(θ))`?

# Let's check!
θ = Var("θ")
x = flip(θ) & flip(θ) & !flip(θ)
var_vals = Valuation(θ => 0.5) # as we train by GD, we need to provide starting a value
loss = -LogPr(x)
train!(var_vals, loss, epochs=200, learning_rate=0.1) # mutates var_vals
@test compute_mixed(var_vals, θ) ≈ 2/3

# Optional note!
# In practice, we pass learned prs. through sigmoid to bound in [0, 1].
# The above example becomes:
θ = sigmoid(Var("θ_before_sigmoid"))
x = flip(θ) & flip(θ) & !flip(θ)
var_vals = Valuation(Var("θ_before_sigmoid") => 0)
loss = -LogPr(x)  # symbolic version of log(pr(...))
train!(var_vals, loss, epochs=2000, learning_rate=0.1)
@test compute_mixed(var_vals, θ) ≈ 2/3

################################################################################
# Approximating datasets
################################################################################

# Consider the following probabilistic program with holes. What probability
# will cause x to be true 2/3 of the time?
p_before_sigmoid = Var("p_before_sigmoid")
p = sigmoid(p_before_sigmoid)
b = @dice_ite if flip(p) true else flip(0.5) end

# We can match this dataset...
dataset = [true, true, false]

# ...by maximizing this value
antiloss = LogPr(prob_equals(b, true)) + LogPr(prob_equals(b, true)) + LogPr(prob_equals(b, false))

var_vals = Valuation(p_before_sigmoid => 0)
train!(var_vals, -antiloss; epochs=2000, learning_rate=0.1)
@test compute_mixed(var_vals, p) ≈ 1/3

# Equivalently, we can use `mle_loss`:
loss = mle_loss([prob_equals(b, x) for x in dataset])
var_vals = Valuation(p_before_sigmoid => 0)
train!(var_vals, loss; epochs=2000, learning_rate=0.1)
@test compute_mixed(var_vals, p) ≈ 1/3

# Two ways to "check our work" by seeing the original progam's probability.
# The program is true 2/3 of the time, as desired!
pr_mixed(var_vals)(b)  # true  => ~ 2/3
@test compute_mixed(var_vals, exp(LogPr(b))) ≈ 2/3

# Here's an example for ints. Lets say we build an int whose bits are flips such
# that it has a uniform distribution over 0, 2, 4, ..., 14.
pre_sigmoid_probs = [Var("b$(i)") for i in 1:4]
probs = [sigmoid(psp) for psp in pre_sigmoid_probs]
n = DistUInt{4}([flip(prob) for prob in probs])

dataset = [DistUInt{4}(even) for even in 0:2:14]
loss = mle_loss([prob_equals(n, x) for x in dataset])

# Train
var_vals = Valuation(psp => 0 for psp in pre_sigmoid_probs)
train!(var_vals, loss; learning_rate=0.1, epochs=2000)

# Check the desired probabilities
@test [compute_mixed(var_vals, prob) for prob in probs] ≈ [0.5, 0.5, 0.5, 0.000626043181613181]

end
