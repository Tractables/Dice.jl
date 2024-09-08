# Demo of using BDD MLE to learn flip probs for nat list of uniform length.
using Dice

# Define inductive datatype for nat lists
@inductive DistNatList DistNil() DistCons(DistUInt32, DistNatList)

function length(l::DistNatList)
    @match l [
        DistNil() -> DistUInt32(0),
        DistCons(x, xs) -> DistUInt32(1) + length(xs),
    ]
end

# Our generator for nat lists
function gen_list(size)
    size == 0 && return DistNil()

    # After understanding this demo as-written, try replacing `size` in the next
    # line with a constant, which would force all sizes to use the same
    # probability. This would restrict the distribution over list lengths to
    # roughly geometric distributions, so the final distribution wouldn't be as
    # close to the desired (but still better than before training).
    @dice_ite if flip(sigmoid(Var(size)))
        DistNil()
    else
        # The flips used in `uniform` use concrete weights, so we don't learn
        # their probabilities (but we could!).
        DistCons(uniform(DistUInt32, 0, 10), gen_list(size-1))
    end
end

# Top-level size/fuel. For gen_list, this is the max length.
INIT_SIZE = 5

# Build computation graph of Dists. We could inline these definitions at their
# use sites (constructing the computation graph is pure), but this saves a tiny
# bit of work.
list = gen_list(INIT_SIZE)
list_len = length(list)

var_vals = Valuation(Var(size) => 0 for size in 1:INIT_SIZE)

println("Distribution before training:")
display(pr_mixed(var_vals)(list_len))
println()

# Approximate a distribution using KL divergence
desired_dist = [
    DistUInt32(0) => 0.3,
    DistUInt32(2) => 0.2,
    DistUInt32(5) => 0.5
]
loss = kl_divergence(desired_dist, list_len)
train!(var_vals, loss, epochs=1000, learning_rate=0.3)

# Done!
println("Learned flip probability for each size:")
display(Dict(size => compute(var_vals, sigmoid(Var(size))) for size in 1:INIT_SIZE))
println()

println("Distribution over lengths after training:")
display(pr_mixed(var_vals)(list_len))

#==
Distribution before training:
   0 => 0.5
   1 => 0.25
   2 => 0.12500000000000003
   3 => 0.0625
   4 => 0.03125
   5 => 0.03125

Learned flip probability for each size:
Dict{Int64, Float64} with 5 entries:
  5 => 0.3
  4 => 0.00482717
  2 => 0.00678713
  3 => 0.285714
  1 => 0.00678713

Distribution over lengths after training:
DataStructures.DefaultOrderedDict{Any, Any, Float64} with 6 entries:
  5 => 0.490855
  0 => 0.3
  2 => 0.199035
  1 => 0.00337902
  3 => 0.00337718
  4 => 0.00335426
==#
