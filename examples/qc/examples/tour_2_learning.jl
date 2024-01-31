# An introduction to using MLE to learn flip probabilities

################################################################################
# Maximizing expression probabilities
################################################################################
using Revise
using Dice

# What value of θ maximizes `pr(flip(θ) & flip(θ) & !flip(θ))`?

# Let's check!
θ = Var("θ")
x = flip(θ) & flip(θ) & !flip(θ)
var_vals = Valuation(θ => 0.5) # as we train by GD, we need to provide starting a value
loss = -LogPr(x)
train!(var_vals, loss, epochs=200, learning_rate=0.1) # mutates var_vals
compute_mixed(var_vals, θ) # ~ 2/3

# Optional note!
# In practice, we pass learned prs. through sigmoid to bound in [0, 1].
# The above example becomes:
θ = sigmoid(Var("θ_before_sigmoid"))
x = flip(θ) & flip(θ) & !flip(θ)
var_vals = Valuation(Var("θ_before_sigmoid") => 0)
loss = -LogPr(x)  # symbolic version of log(pr(...))
train!(var_vals, loss, epochs=200, learning_rate=0.1)
compute_mixed(var_vals, θ) # ~ 2/3

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
compute_mixed(var_vals, p) # ~ 1/3

# Equivalently, we can use `mle_loss`:
loss = mle_loss([prob_equals(b, x) for x in dataset])
var_vals = Valuation(p_before_sigmoid => 0)
train!(var_vals, loss; epochs=2000, learning_rate=0.1)
compute_mixed(var_vals, p) # ~ 1/3

# Two ways to "check our work" by seeing the original progam's probability.
# The program is true 2/3 of the time, as desired!
pr_mixed(var_vals)(b)  # true  => ~ 2/3
compute_mixed(var_vals, exp(LogPr(b))) # ~ 2/3

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
[compute_mixed(var_vals, prob) for prob in probs] # 0.5, 0.5, 0.5, 0.000626043181613181

################################################################################
###################### TODO: update the rest of this file ######################
################################################################################

# ################################################################################
# # Uniform list lengths
# ################################################################################

# # Consider this recursive function which generates lists up to a certain size
# function gen_list(size)
#     size == 0 && return DistNil(DistUInt32)

#     @dice_ite if flip_for("?")
#         DistNil(DistUInt32)
#     else
#         # The flips used in the uniform aren't tracked via flip_for, so we
#         # don't learn their probabilities.
#         DistCons(uniform(DistUInt32, 0, 10), gen_list(size-1))
#     end
# end

# # What if we want to learn a probability for ? such that the list lengths are
# # uniformly distributed from 0 to 5?

# # Note that the distribution of gen_list depends on the initial size passed to
# # the top call. Let's choose to pass in 5 to the top call since we don't want to
# # generate lists larger than that.

# init_size = 5
# dataset = [DistUInt32(x) for x in 0:init_size]
# generated = len(gen_list(init_size))

# # Distribution over lengths before training
# pr(generated)
# #    0 => 0.5
# #    1 => 0.25
# #    2 => 0.12500000000000003
# #    3 => 0.0625
# #    4 => 0.03125
# #    5 => 0.03125

# bools_to_maximize = AnyBool[prob_equals(generated, x) for x in dataset]
# train_group_probs!(bools_to_maximize)
# get_group_probs()
# #   "?" => 0.25

# reset_flips!()

# ################################################################################
# # Uniform list lengths with dynamic groups
# ################################################################################

# # Suppose instead that we can have the flip probability change depend based on
# # the size in the subcall.
# function gen_list(size)
#     size == 0 && return DistNil(DistUInt32)
    
#     #                     vvvvv changed
#     @dice_ite if flip_for(size)
#         DistNil(DistUInt32)
#     else
#         # The flips used in the uniform aren't tracked via flip_for, so we
#         # don't learn their probabilities.
#         DistCons(uniform(DistUInt32, 0, 10), gen_list(size-1))
#     end
# end

# generated = len(gen_list(init_size))
# bools_to_maximize = AnyBool[prob_equals(generated, x) for x in dataset]
# train_group_probs!(bools_to_maximize)
# get_group_probs()
# # 5 => 0.166667
# # 4 => 0.2
# # 2 => 0.333333
# # 3 => 0.25
# # 1 => 0.5

# ################################################################################
# # Including evidence
# ################################################################################

# # So far, we've been passing a list like [x, y, z, ...] to `train_group_probs`.
# # This chooses flip_for probabilities to maximize Pr(x) * Pr(y) * Pr(z)

# # We can also pass a list of tuples to `train_group_probs`, like:
# #   [(x, evid1), (y, evid2), (z, evid3)]
# # This chooses flip_for probabilities to maximize:
# #   Pr(x given evid1) * Pr(y given evid2) * Pr(z given evid3)

# reset_flips!()

# # Lets say we know that x was sampled an unknown dist. over 1, 2, and 3
# x = @dice_ite begin
#     if flip_for("f1")
#         DistUInt32(1) 
#     elseif flip_for("f2")
#         DistUInt32(2)
#     else
#         DistUInt32(3)
#     end
# end

# # Given that x is odd, what flip probabilities cause x to be uniformly distributed?
# is_odd(x::DistUInt32) = prob_equals(x % DistUInt32(2), DistUInt32(1))
# evid = is_odd(x)
# pr(x, evidence=evid)  # 1 => 0.6667, 3 => 0.3333 - not what we want

# train_group_probs!(
#     [
#         (prob_equals(x, DistUInt32(1)), evid),
#         (prob_equals(x, DistUInt32(3)), evid),
#         # Datapoints that indicate x is 2 have no effect under an observation
#         # that removes these worlds
#         (prob_equals(x, DistUInt32(2)), evid),
#         (prob_equals(x, DistUInt32(2)), evid),
#     ]
# )
# get_group_probs()

# pr(x, evidence=evid) # 1 => 0.5, 3 => 0.5

# # More realistic examples for this include demo_sortednatlist.jl and
# # demo_bst.jl.
