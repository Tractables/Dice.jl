
export DistFix

struct DistFix
    mgr
    number::DistInt
    point::Int   
end

function DistFix(b::DistInt, p::Int)
    DistFix(b.mgr, b, p)
end

function infer(d::DistFix)
    point = d.point
    mb = max_bits(d.number)
    ans = Vector(undef, 2^mb)
    non_zero_index = 0
    for i=0:2^mb - 1
        a = infer(prob_equals(d.number, i))
        if !(a ≈ 0)
            non_zero_index = i+1
        end
        ans[i + 1] = (i/2^point, a)
    end
    ans[1:non_zero_index]
end


