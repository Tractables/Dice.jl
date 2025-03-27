# Tour of Alea.jl by example

# Setup testing
using Test
using Alea
function Base.isapprox(d1::AbstractDict, d2::AbstractDict)
    issetequal(keys(d1), keys(d2)) && all(isapprox(d1[k], d2[k],rtol=0.01) for k in keys(d1))
end
@testset "tour_1_core" begin

################################################################################
# Basics
################################################################################

# The fundamental datatype in Alea.jl is `Dist{Bool}`, which represents a
# distribution over booleans.

# `flip(p)` can be used create a random variable ~ Bernoulli(p)
x = flip(0.7)

# We can use `pr(dist)` on a distribution find the dictionary from possible
# values to probabilities.
@test pr(x) ≈ Dict(false => 0.3, true => 0.7)
@test pr(x | true) ≈ Dict(true => 1.0)

# We can use &, |, ^, ! to perform computation on DistBools.
@test pr(flip(0.5) & flip(0.1))[true] ≈ 0.05

# We can find conditional probabilities using the `evidence` keyword arg
x = flip(0.5)
y = flip(0.1)
# Pr[X & Y given X]
@test pr(x & y, evidence=x)[true] ≈ 0.1

# The condition of `if` statements can be Dist{Bool} if written inside of the
# @alea_ite macro.
ite_example = @alea_ite begin
    if flip(0.9)
        true
    else
        !flip(0.5)
    end
end
@test pr(ite_example)[true] ≈ 0.95

################################################################################
# Network Verification
################################################################################

# We now have enough to reconstruct the network verification example from the
# Alea paper.
# https://arxiv.org/pdf/2005.09089.pdf#page=6

function diamond(s1)
    @alea_ite begin
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
    for _ in 1:5
        net = diamond(net)
    end
    net
end

net = network()
@test isapprox(pr(net)[true], 0.99975, rtol=0.001)


################################################################################
# Ints
################################################################################

# DistUInts represent distributions over unsigned integers.
dist = pr(
    @alea_ite if flip(0.3)
        DistUInt32(7)
    else
        DistUInt32(3)
    end
)
@test dist ≈ Dict(7 => 0.3, 3 => 0.7)

# There is no magic here - DistInts are just a different way to interpret a
# joint distribution over multiple bools. We could also write the above as:
i = DistUInt{3}([flip(0.3), true, true]) # typed by width
                                         # most signif. bit first
@test pr(i) ≈ Dict(7 => 0.3, 3 => 0.7)

# A uniform distribution on integers in [start, stop]
x = uniform(DistUInt32, 1, 5)
y = uniform(DistUInt32, 1, 5)
@test pr(x) ≈ Dict(1 => 0.25, 2 => 0.25, 3 => 0.25, 4 => 0.25)

# To check for equality, use prob_equals
product_4 = prob_equals(x * y, DistUInt32(4))
@test pr(product_4)[true] ≈ 0.1875  # 3/16 cases: (1,4), (2,2), (4,1)

is_even(x::DistUInt32) = prob_equals(x % DistUInt32(2), DistUInt32(0))
@test pr(product_4, evidence=is_even(x))[true] ≈ 0.25  # 2/8 cases: (2,2), (4,1)

end
