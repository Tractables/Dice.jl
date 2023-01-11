########################## Tour of Dice.jl by example ##########################

# (This is for an old branch of Dice.jl, grammar_global_mgr, kept for its
# greater support of linguistic features.)

#################################### Basics ####################################

using Dice

# The fundamental datatype in Dice.jl is `DistBool`, which represents a
# distribution over booleans. To create distributions that are constant T/F:
DistBool(true)
DistBool(false)

# `flip(p)` can be used create a random variable ~ Bernoulli(p)
x = flip(0.7)

# We can use `infer(dist)` on a distribution find the dictionary from possible
# values to probabilities.
#
# infer() actually returns a pair where the first value is the above dictionary
# and the second value is the probability of error. Let's ignore the second
# value for now (until it is mentioned again, it will always be 0).
dist, error_p = infer(x)
dist  # Dict(false => 0.3, true => 0.7)

# `infer_bool(x)` is sugar for returning the probability that x is true
infer_bool(x)  # 0.7

# We can use &, |, ^, ! to perform computation on DistBools.
infer_bool(flip(0.5) & flip(0.1))  # 0.05

# We can find conditional probabilities using the `observation` keyword arg
x = flip(0.5)
y = flip(0.1)
infer_bool(x & y, observation=x)  # Pr[X & Y given X] = 0.1

# DistBool(true), DistTrue(), DistBool(1), flip(1), and in most places, `true`,
# are all ways of defining a distribution that is constantly true.
infer_bool(flip(0.5) & flip(0.1) & true)  # 0.05

# Dice.ifelse(condition, then_value, else_value) is a more efficient way of
# writing (condition & then_value) | (!condition & else_value), and also works
# when then_value and else_value are distibutions over non-boolean types (which
# are introduced below).
ite_example = Dice.ifelse(
    flip(0.9),  # condition
    true,  # value if condition is true
    !flip(0.5),  # value if condition is false
)
infer_bool(ite_example)  # 0.95

# The macro @dice_ite desugars traditional control flow (if/else/end) into
# Dice.ifelse. This often helps with readability.
ite_example = @dice_ite begin
    if flip(0.9)
        true
    else
        !flip(0.5)
    end
end
infer_bool(ite_example)  # 0.95

############################# Network Verification #############################

# We now have enough to reconstruct the network verification example from the
# Dice paper.
# https://arxiv.org/pdf/2005.09089.pdf#page=6

function diamond(s1)
    @dice_ite begin
        route = flip(0.5)
        s2 = if route s1 else false end
        s3 = if route false else s1 end
        drop = flip(0.0001)
        # Functions in Julia implicitly return the value of the last expression
        s2 | (s3 & !drop)
    end
end

function network()
    net = true
    for _=1:10
        net = diamond(net)
    end
    net
end

net = network()
infer_bool(net)  # 0.9995001124850018

################################ Ints and Errors ###############################

# DistInts represent distributions over unsigned integers.
dist, error_p = infer(
    @dice_ite if flip(0.3)
        DistInt(7)
    else
        DistInt(3)
    end
)
dist  # Dict(7 => 0.3, 3 => 0.7)

# There is no magic here - DistInts are just a different way to interpret a
# joint distribution over multiple bools. We could also write the above as:
i = DistInt([DistTrue(), DistTrue(), flip(0.3)]) # least significant bit first
dist, error_p = infer(i)
dist  # Dict(7 => 0.3, 3 => 0.7)

# We can also do operations over DistInt. However, errors are possible, such as
# overflow/underflow for addition/subtraction, or div-by-zero, so each operator
# returns a pair. The first value is the resulting DistInt, and the second is a
# DistBool that indicates whether an error happened.
x = DistInt([flip(0.5)])
y = DistInt([flip(0.1)])
x_plus_y, err = x + y

# We then pass err as a keyword argument to infer
dist, error_p = infer(x_plus_y, err=err)

# Observe that the erroneous worlds are excluded from the dist:
dist  # Dict(0 => 0.45, 1 => 0.5)
error_p  # 0.05

# If multiple operations can return an error, we often disjoin the error bits
x_plus_y_plus_z, err2 = x_plus_y + DistInt([flip(0.1)])
dist, error_p = infer(x_plus_y_plus_z, err=err|err2)
dist  # Dict(0 => 0.405, 1 => 0.495)
error_p  # 0.1

# We can avoid overflow by widening
x_plus_y_safe, err = add_bits(x, 1) + y
dist, error_p = infer(x_plus_y_safe, err=err)
dist  # Dict(0 => 0.45, 1 => 0.5, 2 => 0.05)
error_p  # 0.0

# safe_add automatically widens
x_plus_y_safe = safe_add(x, y)

# An aside:
# We can also wrap datatypes with a "DWE" to automatically propagate errors. See
# examples/test_dwe.jl

# To check for equality, we use prob_equals
infer_bool(prob_equals(x, y))  # 0.5

################################ Other datatypes ###############################

# Note that no datatypes are mutable. Each operation returns a modified copy.

# DistChar
# - Wraps a DistInt
# - The set of valid characters is defined by src/lib.char.jl
# - See examples/test_char.jl for example usage

# DistEnum
# - Wraps a DistInt. Its interpretation is determined by some Julia Enum
# - See examples/test_enum.jl for example usage

# DistVector
# - A vector with a probabilistic size and contents
# - 1-indexed, like Julia's Vector
# - Getting and setting an element returns a pair whose second element indicates
#   an out-of-bounds error.
# - Get an element with typical square brackets
# - Set an element with prob_setindex(vec, idx, val)
# - Append with prob_append, concat with prob_extend, check for prefix with
#   prob_startswith.
# - See examples/test_vector.jl for example usage  

# DistTree
# - Contains one dist internally and a vector of DistTree children (an empty
#   vector if a leaf)
# - prob_append_child(tree, newchild), prob_extend_children(tree, newchildren)
#   operate on the children
# - leaves(tree) collects all children
# - See examples/test_tree.jl for example usage
