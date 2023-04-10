# Demo of using BDD MLE to learn flip probs for a BST of uniform depth

using Dice
include("../util.jl")           # print_dict
include("lib/dist_tree.jl")     # DistLeaf, DistBranch, depth
include("lib/unif_between.jl")  # unif

# Return tree, evid pair
function gen_bst(size, lo, hi)
    size == 0 && return DistLeaf(), true

    # Try changing the parameter to flip_for to a constant, which would force
    # all sizes to use the same probability.
    @dice_ite if flip_for(size)
        DistLeaf(), true
    else
        # The flips used in the uniform aren't tracked via flip_for, so we
        # don't learn their probabilities (this is on purpose - we could).
        x, x_evid = unif(lo, hi)
        l, l_evid = gen_bst(size-1, lo, x)
        r, r_evid = gen_bst(size-1, x, hi)
        DistBranch(x, l, r), x_evid | l_evid | r_evid
    end
end

# Top-level size/fuel. For gen_bst, this is the max depth.
INIT_SIZE = 3

# Dataset over the desired property to match. Below is a uniform distribution
# over sizes.
DATASET = [DistUInt32(x) for x in 0:INIT_SIZE]

# Use Dice to build computation graph
gen() = gen_bst(
    INIT_SIZE,
    DistUInt32(1),
    DistUInt32(2 * INIT_SIZE),
)
tree, evid = gen()
tree_depth = depth(x)

println("Distribution before training:")
print_dict(pr(tree_depth, evidence=evid))
println()

cond_bools_to_maximize = [
    (prob_equals(tree_depth, x), evid)
    for x in DATASET
]
train_group_probs!(cond_bools_to_maximize)

# Done!
println("Learned flip probability for each size:")
print_dict(get_group_probs())
println()

println("Distribution over depths after training:")
tree, evid = gen()
tree_depth = depth(x)
print_dict(pr(tree_depth, evidence=evid))
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
   1 => 0.4221209887029583
   2 => 0.1300886284852543
   3 => 0.016641427530024785

Distribution over depths after training:
   1 => 0.2500000000000004
   2 => 0.2500000000000004
   0 => 0.25000000000000017
   3 => 0.24999999999999972

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
