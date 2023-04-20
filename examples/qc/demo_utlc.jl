# Using BDD MLE to learn flip probs for closed UTLC exprs of uniform AST depth

using Dice
include("../util.jl")           # print_dict
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
    # Generate Var
    var, var_evid = @dice_ite if in_scope.len > DistUInt32(0)
        # Uniformly choose variable in scope
        name, name_evid = choice(in_scope)
        DistVar(name), name_evid
    else
        # If we run out of fuel and nothing is in scope, just return id fn
        DistAbs(DistString("x"), DistVar(DistString("x"))), true
    end

    # Fuel check
    size == 0 && return var, var_evid

    # Generate Abs args
    fresh = gen_name()
    e, e_evid = gen_utlc(size-1, prob_append(in_scope, fresh))

    # Generate App args
    e1, e1_evid = gen_utlc(size-1, in_scope)
    e2, e2_evid = gen_utlc(size-1, in_scope)

    # Evidence must be lifted out of probabilistic branches
    evid = var_evid & e_evid & e1_evid & e2_evid

    @dice_ite if flip_for(size) & (in_scope.len > DistUInt32(0))
        var, evid
    elseif flip(2/3)  # fix weight between Abs and App
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
print_dict(pr(e_depth, evidence=evid))
println()

cond_bools_to_maximize = [
    (prob_equals(e_depth, x), evid)
    for x in DATASET
]
train_group_probs!(cond_bools_to_maximize)

# Done!
println("Learned flip probability for each size:")
print_dict(get_group_probs())
println()

println("Distribution over depths after training:")
e, evid = gen()
e_depth = ast_depth(e)
print_dict(pr(e_depth, evidence=evid))
println()

println("A few sampled exprs:")
for _ in 1:10
    expr = sample((e, evid))
    println(utlc_str(expr))
    # println(print_tree(expr))  # concrete AST
end

#==
Distribution before training:
   1 => 0.3333333333333333
   4 => 0.2965619796424217
   2 => 0.1759259259259259
   3 => 0.12367826931870127
   5 => 0.07050049177961776

Learned flip probability for each size:
   1 => 0.6979495720875983
   2 => 0.5243949811082593
   4 => 0.5
   3 => 0.3485623155826433

Distribution over depths after training:
   4 => 0.23237487705509566
   2 => 0.2323748770550956
   1 => 0.23237487705509552
   3 => 0.23237487705509546
   5 => 0.07050049177961776

A few sampled exprs:
λb.b b
(λb.b) (λb.b) (λa.a)
(λa.λc.c) (λc.c c) (λc.c)
(λa.λc.a) ((λa.a) ((λx.x) (λx.x))) ((λc.c) (λb.b) (λb.b))
λa.a
(λb.b) ((λa.a) (λc.c)) (λc.c)
(λa.a) ((λa.λa.a) (λb.b))
λa.λb.a
λb.b
λc.λb.c
==#
