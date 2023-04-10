# Demo of using BDD MLE to learn flip probs for a sorted nat list of uniform length.

using Dice
include("../util.jl")           # print_dict
include("lib/dist_list.jl")     # DistNil, DistCons, len
include("lib/unif_between.jl")  # unif

# Return a list, evid pair
function gen_sorted_list(size, lo, hi)
    size == 0 && return DistNil(), true
    
    # Try changing the parameter to flip_for to a constant, which would force
    # all sizes to use the same probability.
    @dice_ite if flip_for(size)
        DistNil(), true
    else
        # The flips used in the uniform aren't tracked via flip_for, so we
        # don't learn their probabilities (this is on purpose - we could).
        x, x_evid = unif(lo, hi)
        xs, xs_evid = gen_sorted_list(size-1, x, hi)
        DistCons(x, xs), x_evid & xs_evid
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
gen() = gen_sorted_list(
    INIT_SIZE,
    DistUInt32(1),
    DistUInt32(INIT_SIZE),
)
list, evid = gen()
list_len = len(list)

println("Distribution before training:")
print_dict(pr(list_len, evidence=evid))
println()

cond_bools_to_maximize = [
    (prob_equals(list_len, x), evid)
    for x in DATASET
]
train_group_probs!(cond_bools_to_maximize)

# Done!
println("Learned flip probability for each size:")
print_dict(get_group_probs())
println()

println("Distribution over lengths after training:")
list, evid = gen()
list_len = len(list)
print_dict(pr(list_len, evidence=evid))
println()

include("lib/sample.jl")  # sample
println("A few sampled lists:")
l = gen()
for _ in 1:3
    print_tree(sample(l))
    println()
end

#==
Distribution before training:
   0 => 0.6043859955930188
   1 => 0.30219299779650943
   2 => 0.07554824944912734
   3 => 0.014689937392885868
   4 => 0.0024483228988143105
   5 => 0.0007344968696442925

Learned flip probability for each size:
   1 => 0.2307692307692313
   2 => 0.07142857142857169
   3 => 0.02702702702702712
   4 => 0.013333333333333386
   5 => 0.013157894736842155

Distribution over lengths after training:
   0 => 0.16666666666666674
   1 => 0.16666666666666674
   2 => 0.1666666666666666
   3 => 0.1666666666666666
   4 => 0.1666666666666663
   5 => 0.1666666666666657

A few sampled lists:
Cons
├── 2
└── Cons
    ├── 2
    └── Cons
        ├── 2
        └── Cons
            ├── 2
            └── Nil

Cons
├── 1
└── Cons
    ├── 2
    └── Cons
        ├── 2
        └── Cons
            ├── 5
            └── Nil

Cons
├── 4
└── Nil
==#
