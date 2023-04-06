# Demo of using BDD MLE to learn flip probs for a BST of uniform depth

using Dice

# Utils
include("lib/dict_vec.jl")
include("../util.jl")

# Support DistTree
include("lib/inductive.jl")
include("lib/dist_tree.jl")

# Support conditional BDD differentiation
include("lib/cudd_view.jl")
include("lib/cudd_diff.jl")

# Track flip groups
include("lib/compile.jl")
include("lib/flip_groups.jl")
include("lib/train_group_probs.jl")

include("lib/unif_between.jl")

# Return tree, evid pair
function gen_bst(size, lo, hi)
    size == 0 && return EvidMonad.ret(DistLeaf())

    # Try changing the parameter to flip_for to a constant, which would force
    # all sizes to use the same probability.
    @dice_ite if flip_for(size)
        EvidMonad.ret(DistLeaf())
    else
        # The flips used in the uniform aren't tracked via flip_for, so we
        # don't learn their probabilities (this is on purpose - we could).
        mx = unif(lo, hi)
        ml = EvidMonad.bind(mx, x -> gen_bst(size-1, lo, x))
        mr = EvidMonad.bind(mx, x -> gen_bst(size-1, x, hi))
        liftM(EvidMonad, DistBranch)(mx, ml, mr)
    end
end


# Top-level size/fuel. For gen_list, this is the max length.
INIT_SIZE = 3

# Dataset over the desired property to match. Below is a uniform distribution
# over sizes.
DATASET = [DistUInt32(x) for x in 0:INIT_SIZE]

# Training hyperparams
EPOCHS = 500
LEARNING_RATE = 0.1

# Use Dice to build computation graph
gen() = gen_bst(
    INIT_SIZE,
    DistUInt32(1),
    DistUInt32(2 * INIT_SIZE),
)
x = gen()
generated = liftM(EvidMonad, depth)(x)

println("Distribution before training:")
print_dict(pr(generated))
println()

cond_bools_to_maximize = Cond{<:AnyBool}[
    liftM(EvidMonad, prob_equals)(generated, EvidMonad.ret(x))
    for x in DATASET
]
train_group_probs!(cond_bools_to_maximize, EPOCHS, LEARNING_RATE)

# Done!
println("Learned flip probability for each size:")
print_dict(Dict(group => sigmoid(psp) for (group, psp) in group_to_psp))
println()

println("Distribution over depths after training:")
generated = liftM(EvidMonad, depth)(gen())
print_dict(pr(generated))
println()

include("lib/sample.jl")
println("A few sampled trees:")
l = gen()
for _ in 1:3
    print_tree(sample(l))
    println()
end


#==
Distribution before training:
   0 => 0.7529011474060479
   1 => 0.188225286851512
   2 => 0.035553665294174475
   3 => 0.023319900448265686

Learned flip probability for each size:
   1 => 0.4221866018509798
   2 => 0.13012499953148837
   3 => 0.016650759153960585

Distribution over depths after training:
   0 => 0.2500235318247399
   1 => 0.2500207856193543
   2 => 0.2500178265709582
   3 => 0.24993785598494764

A few sampled trees:
Branch
├── 2
├── Leaf
└── Branch
    ├── 4
    ├── Branch
    │   ├── 3
    │   ├── Leaf
    │   └── Leaf
    └── Leaf

Leaf

Branch
├── 1
├── Leaf
└── Branch
    ├── 6
    ├── Leaf
    └── Leaf
==#
