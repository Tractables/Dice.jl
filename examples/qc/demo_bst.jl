# Demo of using BDD MLE to learn flip probs for a BST of uniform depth

using Dice
include("../util.jl")           # print_dict
include("lib/dist_tree.jl")     # DistLeaf, DistBranch, depth
include("lib/unif_between.jl")  # unif
include("lib/sample.jl")        # sample

# Return tree, evid pair
function gen_bst(size, lo, hi)
    size == 0 && return DistLeaf(), true

    x, x_evid = unif(lo, hi)
    l, l_evid = gen_bst(size-1, lo, x)
    r, r_evid = gen_bst(size-1, x, hi)
    evid = x_evid & l_evid & r_evid

    # Try changing the parameter to flip_for to a constant, which would force
    # all sizes to use the same probability.
    @dice_ite if flip_for(size)
        DistLeaf(), evid
    else
        # The flips used in the uniform aren't tracked via flip_for, so we
        # don't learn their probabilities (this is on purpose - we could).
        DistBranch(x, l, r), evid
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
tree_depth = depth(tree)

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
tree_depth = depth(tree)
print_dict(pr(tree_depth, evidence=evid))
println()

println("A few sampled trees:")
for _ in 1:3
    print_tree(sample((tree, evid)))
    println()
end

#==
Distribution before training:
   0 => 0.49999999999999994
   3 => 0.30468750000000006
   1 => 0.12499999999999997
   2 => 0.0703125

Learned flip probability for each size:
   1 => 0.7522142306508817
   2 => 0.5773502691896257
   3 => 0.25

Distribution over depths after training:
   0 => 0.2500000000000004
   1 => 0.24999999999999994
   2 => 0.24999999999999994
   3 => 0.24999999999999994

A few sampled trees:
Branch
├── 2
├── Branch
│   ├── 2
│   ├── Leaf
│   └── Leaf
└── Branch
    ├── 5
    ├── Leaf
    └── Branch
        ├── 6
        ├── Leaf
        └── Leaf

Branch
├── 3
├── Leaf
└── Branch
    ├── 3
    ├── Leaf
    └── Branch
        ├── 3
        ├── Leaf
        └── Leaf

Branch
├── 2
├── Leaf
└── Leaf
==#
