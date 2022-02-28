
export DistFix

struct DistFix <: Dist{Int}
    mgr
    number::DistInt
    point::Int   
end

function DistFix(b::Vector, p::Int)
    DistFix(b[1].mgr, DistInt(b), p)
end

function DistFix(mgr, a::Int, p::Int)
    DistFix(DistInt(mgr, a).bits, p)
end

function prob_equals(x::DistFix, y::DistFix)
    @assert x.point == y.point
    prob_equals(x.number, y.number)
end

function ifelse(cond::DistBool, then::DistFix, elze::DistFix)
    @assert then.point == elze.point
    DistFix(cond.mgr, ifelse(cond, then.number, elze.number), then.point)
end

function Base.:+(p1::DistFix, p2::DistFix)
    @assert p1.point == p2.point
    ans = p1.number + p2.number
    DistFix(ans[1].bits, p1.point), ans[2]
end

function Base.:-(p1::DistFix, p2::DistFix)
    @assert p1.point == p2.point
    ans = p1.number - p2.number
    DistFix(ans[1].bits, p1.point), ans[2]
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

function condinfer(d::DistFix, b::DistBool)
    point = d.point
    mb = max_bits(d.number)
    ans = Vector(undef, 2^mb)
    non_zero_index = 0
    for i=0:2^mb - 1
        a = infer(Cond(prob_equals(d.number, i), b))
        if !(a ≈ 0)
            non_zero_index = i+1
        end
        ans[i + 1] = (i/2^point, a)
    end
    ans[1:non_zero_index]
end
