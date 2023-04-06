# Demo of using BDD MLE to learn flip probs for nat list of uniform length.

using Dice

# Utils
include("lib/dict_vec.jl")
include("../util.jl")

# Support DistList
include("lib/inductive.jl")
include("lib/dist_list.jl")

# Support conditional BDD differentiation
include("lib/cudd_view.jl")
include("lib/cudd_diff.jl")

# Track flip groups
include("lib/compile.jl")
include("lib/flip_groups.jl")
include("lib/train_group_probs.jl")


function gen_list(size)
    size == 0 && return DistNil()

    # Try changing the parameter to flip_for to a constant, which would force
    # all sizes to use the same probability.
    @dice_ite if flip_for(size)
        DistNil()
    else
        # The flips used in the uniform aren't tracked via flip_for, so we
        # don't learn their probabilities (this is on purpose - we could).
        DistCons(uniform(DistUInt32, 0, 10), gen_list(size-1))
    end
end


# Top-level size/fuel. For gen_list, this is the max length.
INIT_SIZE = 5

# Dataset over the desired property to match. Below is a uniform distribution
# over sizes.
DATASET = [DistUInt32(x) for x in 0:INIT_SIZE]

# Training hyperparams
EPOCHS = 500
LEARNING_RATE = 0.1

# Use Dice to build computation graph
generated = len(gen_list(INIT_SIZE))

println("Distribution before training:")
print_dict(pr(generated))
println()

bools_to_maximize = AnyBool[prob_equals(generated, x) for x in DATASET]
train_group_probs!(bools_to_maximize, EPOCHS, LEARNING_RATE)

# Done!
println("Learned flip probability for each size:")
print_dict(Dict(group => sigmoid(psp) for (group, psp) in group_to_psp))
println()

println("Distribution over lengths after training:")
print_dict(pr(len(gen_list(INIT_SIZE))))

#==
Distribution over lengths before training:
   0 => 0.5
   1 => 0.25
   2 => 0.12500000000000003
   3 => 0.0625
   4 => 0.03125
   5 => 0.03125

Learned flip probability for each size:
   1 => 0.5
   2 => 0.33333333333333354
   3 => 0.2500000000000003
   4 => 0.2000000000000002
   5 => 0.16666666666666685

Distribution over lengths after training:
   0 => 0.16666666666666685
   1 => 0.1666666666666668
   2 => 0.1666666666666668
   3 => 0.16666666666666663
   4 => 0.1666666666666665
   5 => 0.1666666666666665
==#
