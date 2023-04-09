# An introduction to using MLE to learn flip probabilities

################################################################################
# Setup
################################################################################

using Dice

# For print_dict
include("../util.jl")

# Inductive datatypes
include("lib/inductive.jl")
include("lib/dist_tree.jl")

# Support conditional BDD differentiation
include("lib/dict_vec.jl")
include("lib/cudd_view.jl")
include("lib/cudd_diff.jl")

# Track flip groups
include("lib/compile.jl")
include("lib/flip_groups.jl")
include("lib/train_group_probs.jl")


################################################################################
# Maximizing expression probabilities
################################################################################

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

reset_flips!()  # clear registered flips

# If the flips above can have different groups, each can take on a
# different probability.
x = flip_for("a") & flip_for("b") & !flip_for("c")
train_group_probs!([x])
print_dict(get_group_probs())
# a => 0.9966337256742784
# b => 0.9966337256742784
# c => 0.003366274325721429

# Not surprising! We can also keep training to get closer to 1, 1, 0.
train_group_probs!(
	[x],
	10000, # epochs
	3.0    # learning rate
)
print_dict(get_group_probs())
# a => 0.9999669960226594
# b => 0.9999669960226594
# c => 3.3003977340565305e-5

reset_flips!()


################################################################################
# Approximating datasets
################################################################################

# Consider the following probabilistic program with holes. What probability
# will cause x to be true 2/3 of the time?
x = @dice_ite if flip_for("?")
    true
else
    flip(0.5)
end

# We can match this dataset...
dataset = [true, true, false]

# ...by maximizing these distributions over bools:
bools_to_maximize = [prob_equals(x, y) for y in dataset]

train_group_probs!(bools_to_maximize)
print_dict(get_group_probs())  # ? => 0.3333333333333336

# Again - we can also constrain multiple flips to have the same probability
reset_flips!()
x = @dice_ite if flip_for("?")
    true
else
    flip_for("?")
end
train_group_probs!([prob_equals(x, y) for y in dataset])
print_dict(get_group_probs()) # ? => 0.42264973081037427
# This value for ? isn't as intuitive. Let's double-check the distribution:
pr(@dice_ite if flip(0.42265) true else flip(0.42265) end)
# false => 0.333333
# true  => 0.666667
pr(x)
	



simple dependency

function f(x)
	if x > 0
		f(x - 1)
if flip_for(x) flip(0.5) else flip(0.3) end
end

train!(
	[prob_eq(f(1), true)
	prob_eq(f(1), false)
	prob_eq(f(2), false)
)

result:
1 => ??
2 =>  ??

recursive function that calls smaller 

list

flips = [...]
list = generateList(...) # depends on flips
train_flip_probs!(flips, wrt=[
prob_equals(list, [1, 2, 3]),
prob_equals(list, [2, 3, 4]),
])

