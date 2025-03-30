# Demo of using BDD MLE to learn flip probs for a BST of uniform depth

using Dice

@inductive DistTree DistLeaf() DistBranch(DistUInt32, DistTree, DistTree)

function depth(l::DistTree)
    @match(l, [
        DistLeaf() -> DistUInt32(0),
        DistBranch(x, l, r) -> begin
            dl, dr = depth(l), depth(r)
            @alea_ite if dl > dr
                DistUInt32(1) + dl
            else
                DistUInt32(1) + dr
            end
        end
    ])
end

var_vals = Valuation()
adnodes_of_interest = Dict{String, ADNode}()
function register_weight!(s)
    var = Var("$(s)_before_sigmoid")
    var_vals[var] = 0
    weight = sigmoid(var)
    adnodes_of_interest[s] = weight
    weight
end

# Return tree
function gen_bst(size, lo, hi)
    @alea_ite if size == 0 || flip(register_weight!("sz$(size)"))
        DistLeaf()
    else
        x = unif(lo, hi)
        DistBranch(x, gen_bst(size-1, lo, x), gen_bst(size-1, x, hi))
    end
end

# Top-level size/fuel. For gen_bst, this is the max depth.
INIT_SIZE = 3

# Dataset over the desired property to match. Below is a uniform distribution
# over sizes.
DATASET = [DistUInt32(x) for x in 0:INIT_SIZE]

# Use Dice to build computation graph
tree = gen_bst(
    INIT_SIZE,
    DistUInt32(1),
    DistUInt32(2 * INIT_SIZE),
)
tree_depth = depth(tree)

println("Distribution before training:")
display(pr_mixed(var_vals)(tree_depth))
println()

train!(var_vals, mle_loss([prob_equals(tree_depth, x) for x in DATASET]), epochs=1000, learning_rate=0.3)

# Done!
println("Learned flip probability for each size:")
vals = compute(var_vals, values(adnodes_of_interest))
show(Dict(s => vals[adnode] for (s, adnode) in adnodes_of_interest))
println()
println()

println("Distribution over depths after training:")
display(pr_mixed(var_vals)(tree_depth))
println()

println("A few sampled trees:")
with_concrete_ad_flips(var_vals, tree) do
    for _ in 1:3
        print_tree(sample_default_rng(tree))
        println()
    end
end

#==
Distribution before training:
DataStructures.DefaultOrderedDict{Any, Any, Float64} with 4 entries:
  0 => 0.5
  3 => 0.304688
  1 => 0.125
  2 => 0.0703125

Learned flip probability for each size:
Dict("sz1" => 0.7522142306508817, "sz2" => 0.5773502691896257, "sz3" => 0.25000000000000006)

Distribution over depths after training:
DataStructures.DefaultOrderedDict{Any, Any, Float64} with 4 entries:
  0 => 0.25
  3 => 0.25
  1 => 0.25
  2 => 0.25

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
