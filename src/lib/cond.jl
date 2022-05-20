# Conditional Inference
export Cond

# struct CondBool <: Dist{Bool}
#     b1::DistBool
#     b2::DistBool
# end

struct Cond{T}
    b1::Dist{T}
    b2::DistBool
end

# function infer(c::CondBool)
#     infer(c.b1 & c.b2)/infer(c.b2)
# end

# struct CondInt <: Dist{Int}
#     b1::DistInt
#     b2::DistBool
# end

function infer(c::Cond)
    condinfer(c.b1, c.b2)
end

function expectation(c::Cond)
    expectation(c.b1, c.b2)
end

function variance(c::Cond)
    variance(c.b1, c.b2)
end

bools(i::Cond) = vcat(bools(i.b1), bools(i.b2))