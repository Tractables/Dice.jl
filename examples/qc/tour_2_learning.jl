# An introduction to using MLE to learn flip probabilities

################################################################################
# Maximizing expression probabilities
################################################################################

using Dice

# What value for ? maximizes the probability of the following expression?
#   flip(?) & flip(?) & !flip(?)

# Let's check!
x = flip_for("?") & flip_for("?") & !flip_for("?")
train_group_probs!([x])
get_group_probs()  # ? => 0.666667

# What just happened?
# - `flip_for(group)` registers a flip that we want to learn the probability of.
#   flips in the same group are still independent, but must share their
#    probability.
# - `train_group_probs!(bools)` performs maximum likelihood estimation to train
#   the parameters of registered flips, to maximize the product of the
#   probabilities of the bools

reset_flips!()  # call this before the first flip_for of the next program

# If the flips above can have different groups, each can take on a
# different probability.
x = flip_for("a") & flip_for("b") & !flip_for("c")
train_group_probs!([x])
get_group_probs()
# a => 0.996634
# b => 0.996634
# c => 0.00336627

# Not surprising! We can also keep training to get closer to 1, 1, 0.
train_group_probs!(
	[x],
	10000, # epochs
	3.0    # learning rate
)
get_group_probs()
# a => 0.999967
# b => 0.999967
# c => 3.3004e-5

reset_flips!()


################################################################################
# Approximating datasets
################################################################################

# Consider the following probabilistic program with holes. What probability
# will cause x to be true 2/3 of the time?
b = @dice_ite if flip_for("?") true else flip(0.5) end

# We can match this dataset...
dataset = [true, true, false]

# ...by maximizing these distributions over bools:
bools_to_maximize = [prob_equals(b, x) for x in dataset]
train_group_probs!(bools_to_maximize)
get_group_probs()  # ? => 0.33333

# We can also check how close we are by performing normal Dice inference.
# Let's back up:
reset_flips!()
b = @dice_ite if flip_for("?") true else flip(0.5) end

# By default, `flip_for`s have a probability of 0.5
pr(b)  # true => 0.75

# `train_group_probs` mutates the probabilities of `flip_for`s (but not `flip`s)
train_group_probs!([prob_equals(b, x) for x in dataset])

# The program is true 2/3 of the time, as desired!
pr(b)  # true  => 0.666667

reset_flips!()

# As before, we can also constrain multiple flips to have the same probability
#                                        vvvvvvvvvvvv changed
b = @dice_ite if flip_for("?") true else flip_for("?") end
train_group_probs!([prob_equals(b, x) for x in dataset])
get_group_probs() # ? => 0.42264973081037427
pr(b)  # true => 0.666667

reset_flips!()

# Here's an example for ints. Lets say we build an int whose bits are flips such
# that it has a uniform distribution over 0, 2, 4, ..., 14.
n = DistUInt{4}([flip_for("b$(i)") for i in 1:4])
dataset = [DistUInt{4}(even) for even in 0:2:14]
bools_to_maximize = [prob_equals(n, x) for x in dataset]
train_group_probs!(bools_to_maximize)
get_group_probs()
# "b1" => 0.5
# "b2" => 0.5
# "b3" => 0.5
# "b4" => 0.000416122

reset_flips!()


################################################################################
# Uniform list lengths
################################################################################

# Load support for distributions over cons lists
include("lib/dist_list.jl")

# Consider this recursive function which generates lists up to a certain size
function gen_list(size)
    size == 0 && return DistNil()

    @dice_ite if flip_for("?")
        DistNil()
    else
        # The flips used in the uniform aren't tracked via flip_for, so we
        # don't learn their probabilities.
        DistCons(uniform(DistUInt32, 0, 10), gen_list(size-1))
    end
end

# What if we want to learn a probability for ? such that the list lengths are
# uniformly distributed from 0 to 5?

# Note that the distribution of gen_list depends on the initial size passed to
# the top call. Let's choose to pass in 5 to the top call since we don't want to
# generate lists larger than that.

init_size = 5
dataset = [DistUInt32(x) for x in 0:init_size]
generated = len(gen_list(init_size))

# Distribution over lengths before training
pr(generated)
#    0 => 0.5
#    1 => 0.25
#    2 => 0.12500000000000003
#    3 => 0.0625
#    4 => 0.03125
#    5 => 0.03125

bools_to_maximize = AnyBool[prob_equals(generated, x) for x in dataset]
train_group_probs!(bools_to_maximize)
get_group_probs()
#   "?" => 0.25

reset_flips!()

################################################################################
# Uniform list lengths with dynamic groups
################################################################################

# Suppose instead that we can have the flip probability change depend based on
# the size in the subcall.
function gen_list(size)
    size == 0 && return DistNil()
    
    #                     vvvvv changed
    @dice_ite if flip_for(size)
        DistNil()
    else
        # The flips used in the uniform aren't tracked via flip_for, so we
        # don't learn their probabilities.
        DistCons(uniform(DistUInt32, 0, 10), gen_list(size-1))
    end
end

generated = len(gen_list(init_size))
bools_to_maximize = AnyBool[prob_equals(generated, x) for x in dataset]
train_group_probs!(bools_to_maximize)
get_group_probs()
#   "?" => 0.25


################################################################################
# Including evidence
################################################################################

# So far, we've been passing a list like [x, y, z, ...] to `train_group_probs`.
# This chooses flip_for probabilities to maximize Pr(x) * Pr(y) * Pr(z)

# We can also pass a list of tuples to `train_group_probs`, like:
#   [(x, evid1), (y, evid2), (z, evid3)]
# This chooses flip_for probabilities to maximize:
#   Pr(x given evid1) * Pr(y given evid2) * Pr(z given evid3)

# Examples for this include demo_sortednatlist.jl and demo_bst.jl.

# TODO: What's a good small example?
