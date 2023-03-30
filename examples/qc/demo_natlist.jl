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
# Flips id'd by arbitrary values
# ==============================================================================

flips = Dict{Any, Dice.Flip}()

function flip_for(x)
    get!(flips, x) do
        flip(0.5)
    end
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

    @dice_ite if flip_for(size)
        DistNil()
    else
        # The flips used in the uniform aren't tracked via flip_for, so we
        # don't learn their probabilities (this is on purpose - we could).
        DistCons(uniform(DistUInt32, 0, 10), genList(size-1))
    end
end


# ==============================================================================
# main
# ==============================================================================

# Top-level size/fuel. For genList, this is the max length.
INIT_SIZE = 5

# Dataset over the desired property to match. Below is a uniform distribution
# over sizes.
DATASET = [DistUInt32(x) for x in 0:INIT_SIZE]

NUM_ITERS = 100

LEARNING_RATE = 0.01

function main()
    # Use Dice to build computation graph
    empty!(flips)
    len = probLength(genList(INIT_SIZE))
    
    println("Distribution over lengths before training:")
    print_dict(pr(len))
    println()

    # Compile to BDDs
    bools_to_maximize = AnyBool[prob_equals(len, x) for x in DATASET]
    bdds_to_maximize, level_to_flip_id = compile_helper(bools_to_maximize, flips)

    # Learn best flip probs to match dataset
    flip_probs = Dict(f_id => 0.5 for f_id in keys(flips))
    for _ in 1:NUM_ITERS
        flip_probs = step_flip_probs(flip_probs, bdds_to_maximize, level_to_flip_id, LEARNING_RATE)
    end

    # Done!
    println("Learned flip probability for each size:")
    print_dict(flip_probs)
    println()

    println("Distribution over lengths after training:")
    for (f_id, f_prob) in flip_probs
        flips[f_id] = flip(f_prob)
    end
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
   1 => 0.5
   2 => 0.33333343685929784
   3 => 0.2500000000173302
   4 => 0.20000000000000007
   5 => 0.16666666666666666

Distribution over lengths after training:
   3 => 0.16666671842579778
   2 => 0.1666666666782201
   1 => 0.1666666666666667
   0 => 0.16666666666666669
   4 => 0.16666664078132437
   5 => 0.16666664078132437
==#
