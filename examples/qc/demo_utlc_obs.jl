# Using BDD MLE to learn flip probs for closed UTLC exprs of uniform AST depth

using Dice
include("lib/dist_utlc.jl")     # DistVar, DistApp, DistAbs, utlc_str
include("lib/sample.jl")        # sample

function gen_name()
    @dice_ite if flip(1/3)
        DistString("a")
    elseif flip(1/2)
        DistString("b")
    else
        DistString("c")
    end
end

# Return ast, evid pair
function gen_utlc(size, in_scope)
    # Generate Var arg
    name, name_evid = choice_obs(in_scope)

    # Fuel check
    size == 0 && return DistVar(name), name_evid

    # Generate Abs args
    fresh = gen_name()
    e, e_evid = gen_utlc(size-1, prob_append(in_scope, fresh))

    # Generate App args
    e1, e1_evid = gen_utlc(size-1, in_scope)
    e2, e2_evid = gen_utlc(size-1, in_scope)

    # Evidence must be lifted out of probabilistic branches
    evid = name_evid & e_evid & e1_evid & e2_evid

    @dice_ite if flip_for(size) & (in_scope.len > DistUInt32(0))
        DistVar(name), evid
    # Fix weight between Abs and App. We must also always choose Abs if
    # size=1 and the scope is empty so far.
    elseif flip(2/3) | (size==1 & prob_equals(in_scope.len, DistUInt32(0)))
        DistAbs(fresh, e), evid
    else
        DistApp(e1, e2), evid
    end
end

# Top-level size/fuel. For gen_bst, this is the max depth.
INIT_SIZE = 4

# Dataset over the desired property to match. Below is a uniform distribution
# over sizes.
DATASET = [DistUInt32(x) for x in 0:INIT_SIZE]

# Use Dice to build computation graph
gen() = gen_utlc(INIT_SIZE, DistVector{DistString}())

e, evid = gen()
e_depth = ast_depth(e)

println("Distribution before training:")
pr(evid)
display(pr(e_depth, evidence=evid))
println()

cond_bools_to_maximize = [
    (prob_equals(e_depth, x), evid)
    for x in DATASET
]
train_group_probs!(cond_bools_to_maximize)

# Done!
println("Learned flip probability for each size:")
display(get_group_probs())
println()

println("Distribution over depths after training:")
e, evid = gen()
e_depth = ast_depth(e)
display(pr(e_depth, evidence=evid))
println()

println("A few sampled exprs:")
for _ in 1:10
    expr = sample((e, evid))
    println(utlc_str(expr))
    # println(print_tree(expr))  # concrete AST
end

#==
Distribution before training:
   4 => 0.3670624714220393
   1 => 0.3333333333333333
   2 => 0.1759259259259259
   3 => 0.12367826931870127

Learned flip probability for each size:
   1 => 0.7709384509910406
   2 => 0.5673658539871177
   4 => 0.5
   3 => 0.3749999999999999

Distribution over depths after training:
   2 => 0.2500000000000001
   4 => 0.25000000000000006
   1 => 0.2499999999999999
   3 => 0.24999999999999983

A few sampled exprs:
λc.λb.b b
λb.λa.λc.a b
(λa.a) (λa.a)
λb.(λa.λc.c) (b b)
λb.b
λb.b
(λc.c) (λa.λc.λc.c)
(λb.b) (λb.λc.c b)
λb.b
λa.λb.λb.λb.b
==#
