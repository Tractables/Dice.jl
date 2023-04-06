# Demo of using BDD MLE to learn flip probs for a sorted nat list of uniform length.

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

include("lib/unif_between.jl")

# Return list, evid pair
function gen_sorted_list(size, lo, hi)
    size == 0 && return EvidMonad.ret(DistNil())

    # Try changing the parameter to flip_for to a constant, which would force
    # all sizes to use the same probability.
    @dice_ite if flip_for(size)
        EvidMonad.ret(DistNil())
    else
        # The flips used in the uniform aren't tracked via flip_for, so we
        # don't learn their probabilities (this is on purpose - we could).
        mx = unif(lo, hi)
        mxs = EvidMonad.bind(mx, x -> gen_sorted_list(size-1, x, hi))
        liftM2(EvidMonad, DistCons)(mx, mxs)
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
x = gen()
generated = liftM(EvidMonad, len)(x)

println("Distribution before training:")
print_dict(pr(generated))
println()

cond_bools_to_maximize = Cond{<:AnyBool}[
    liftM2(EvidMonad, prob_equals)(generated, EvidMonad.ret(x))
    for x in DATASET
]
train_group_probs!(cond_bools_to_maximize, EPOCHS, LEARNING_RATE)

# Done!
println("Learned flip probability for each size:")
print_dict(Dict(group => sigmoid(psp) for (group, psp) in group_to_psp))
println()

println("Distribution over lengths after training:")
generated = liftM(EvidMonad, len)(gen())
print_dict(pr(generated))
println()

include("lib/sample.jl")
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
   1 => 0.23076992187684997
   2 => 0.07142880101797898
   3 => 0.027027114085751116
   4 => 0.013333375907124311
   5 => 0.013157936194860715

Distribution over lengths after training:
   1 => 0.16666681044677775
   0 => 0.16666681041111409
   2 => 0.16666680794498645
   3 => 0.16666679187862538
   4 => 0.1666667140950012
   5 => 0.16666606522349497

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
