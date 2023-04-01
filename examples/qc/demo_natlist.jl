# Demo of using BDD MLE to learn flip probs for nat list of uniform length.

using Revise
using Dice

include("inductive.jl")
include("dict_vec.jl")
include("cudd_view.jl")
include("cudd_diff.jl")
include("compile.jl")
include("../util.jl")


# ==============================================================================
# Flips whose probability is shared
# ==============================================================================

# Map flip to group of flips that much share a probability
flip_to_group = Dict{Dice.Flip, Any}()

# Prob group to psp ("pre-sigmoid probability")
group_to_psp = Dict{Any, Float64}()

# flip_for(x) and flip_for(y) are always separate flips, but if x == y, then
# they share their probability.
function flip_for(group)
    f = flip(sigmoid(get!(group_to_psp, group, 0.)))
    flip_to_group[f] = group
    f
end


# ==============================================================================
# Define DistList
# ==============================================================================

DistList = InductiveDistType()
DistList.constructors = [
    ("Nil",  []),
    ("Cons", [Dist, DistList]),
]

DistNil()       = construct(DistList, "Nil",  ())
DistCons(x, xs) = construct(DistList, "Cons", (x, xs))

function len(l)
    match(l, [
        "Nil"  => ()      -> DistUInt32(0),
        "Cons" => (x, xs) -> DistUInt32(1) + len(xs),
    ])
end


# ==============================================================================
# gen_list
# ==============================================================================

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


# ==============================================================================
# main
# ==============================================================================

# Top-level size/fuel. For gen_list, this is the max length.
INIT_SIZE = 5

# Dataset over the desired property to match. Below is a uniform distribution
# over sizes.
DATASET = [DistUInt32(x) for x in 0:INIT_SIZE]

EPOCHS = 500
LEARNING_RATE = 0.1

function main()
    global flip_to_group
    global group_to_psp
    empty!(flip_to_group)
    empty!(group_to_psp)

    # Use Dice to build computation graph
    generated_len = len(gen_list(INIT_SIZE))
    
    println("Distribution over lengths before training:")
    print_dict(pr(generated_len))
    println()

    # Compile to BDDs
    bools_to_maximize = AnyBool[prob_equals(generated_len, x) for x in DATASET]
    bdds_to_maximize, level_to_group = compile_helper(bools_to_maximize, flip_to_group)

    # Learn best flip probs to match dataset
    group_to_psp = Dict(group => 0. for group in keys(group_to_psp))
    for _ in 1:EPOCHS
        group_to_psp = step_flip_probs(group_to_psp, bdds_to_maximize, level_to_group, LEARNING_RATE)
    end

    # Done!
    println("Learned flip probability for each size:")
    print_dict(Dict(group => sigmoid(psp) for (group, psp) in group_to_psp))
    println()

    println("Distribution over lengths after training:")
    print_dict(pr(len(gen_list(INIT_SIZE))))
end

main()

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
