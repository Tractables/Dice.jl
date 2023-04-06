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

flip_to_prob_group = Dict{Dice.Flip, Any}()

# Prob group to flip probability
flip_probs = Dict{Any, Float64}()

# flip_for(x) and flip_for(y) are always separate flips, but if x == y, then
# they share their probability.
function flip_for(pg)
    f = flip(get!(flip_probs, pg, 0.5))
    flip_to_prob_group[f] = pg
    f
end


# ==============================================================================
# Define DistNatList
# ==============================================================================

DistNatList = InductiveDistType()
DistNatList.constructors = [
    ("Nil",  []),
    ("Cons", [DistUInt32, DistNatList]),
]

DistNil()       = construct(DistNatList, "Nil",  ())
DistCons(x, xs) = construct(DistNatList, "Cons", (x, xs))

function probLength(l)
    match(l, [
        "Nil"  => ()      -> DistUInt32(0),
        "Cons" => (x, xs) -> DistUInt32(1) + probLength(xs),
    ])
end


# ==============================================================================
# genList
# ==============================================================================

function genList(size)
    size == 0 && return DistNil()

    # Try changing the parameter to flip_for to a constant, which would force
    # all sizes to use the same probability.
    @dice_ite if flip_for(size)
        DistNil()
    else
        # The flips used in the uniform aren't tracked via flip_for, so we
        # don't learn their probabilities (this is on purpose - we could).
        DistCons(uniform(DistUInt32, 0, 10), genList(size-1))
    end
end
@show flip_probs

# ==============================================================================
# main
# ==============================================================================

# Top-level size/fuel. For genList, this is the max length.
INIT_SIZE = 5

# Dataset over the desired property to match. Below is a uniform distribution
# over sizes.
DATASET = [DistUInt32(x) for x in 0:INIT_SIZE]

EPOCHS = 1000
LEARNING_RATE = 0.006

function main()
    # Use Dice to build computation graph
    empty!(flip_to_prob_group)
    len = probLength(genList(INIT_SIZE))
    
    println("Distribution over lengths before training:")
    print_dict(pr(len))
    println()

    # Compile to BDDs
    print
    bools_to_maximize = AnyBool[prob_equals(len, x) for x in DATASET]
    bdds_to_maximize, level_to_prob_group = compile_helper(bools_to_maximize, flip_to_prob_group)
    @show level_to_prob_group
    prob_groups = Set(values(flip_to_prob_group))

    # Learn best flip probs to match dataset
    flip_probs = Dict(pg => rand() for pg in prob_groups)
    for _ in 1:EPOCHS
        flip_probs = step_flip_probs(flip_probs, prob_groups, bdds_to_maximize, level_to_prob_group, LEARNING_RATE)
    end

    # Done!
    println("Learned flip probability for each size:")
    print_dict(flip_probs)
    println()

    println("Distribution over lengths after training:")
    global flip_probs = flip_probs
    print_dict(pr(probLength(genList(INIT_SIZE))))
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
   1 => 0.5000000000000011
   2 => 0.33333333333333365
   3 => 0.25000000000000017
   4 => 0.20000000000000007
   5 => 0.16666666666666669

Distribution over lengths after training:
   4 => 0.16666666666666685
   2 => 0.16666666666666674
   3 => 0.16666666666666674
   1 => 0.1666666666666667
   0 => 0.16666666666666669
   5 => 0.16666666666666613
==#
