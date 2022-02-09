# Conditional Inference
export CondBool, CondInt

struct CondBool <: Dist{Bool}
    b1::DistBool
    b2::DistBool
end

function infer(c::CondBool)
    infer(c.b1 & c.b2)/infer(c.b2)
end

struct CondInt <: Dist{Int}
    b1::ProbInt
    b2::DistBool
end

function infer(c::CondInt)
    d = c.b1
    b = c.b2    
    mb = max_bits(d)
    ans = Vector(undef, 2^mb)
    non_zero_index = 0
    for i=0:2^mb - 1
        a = infer(CondBool(prob_equals(d, i), b))
        if !(a ≈ 0)
            non_zero_index = i+1
        end
        ans[i + 1] = a
    end
    ans[1:non_zero_index]
end