
export DistFixParam

struct DistFixParam{T, F} <: Dist{Int}
    mgr
    number::DistInt
end

function DistFixParam{T, F}(b::Vector) where T where F
    # @assert length(b) == T
    if (length(b) < T)
        DistFixParam{T, F}(b[1].mgr, add_bits(DistInt(b), T - length(b)))
    else
        DistFixParam{T, F}(b[1].mgr, DistInt(b))
    end
end

function DistFixParam{T, F}(mgr, i::Int) where T where F
    @assert i >= 0
    a =  DistInt(mgr, i)
    @assert length(a.bits) <= T
    # a = add_bits(a, T - max_bits(a))
    # @show max_bits(a)
    DistFixParam{T, F}(mgr, a)
end

function ifelse(cond::DistBool, then::DistFixParam{T, F}, elze::DistFixParam{T, F}) where T where F
    DistFixParam{T, F}(cond.mgr, ifelse(cond, then.number, elze.number))
end

function prob_equals(p1::DistFixParam{T, F}, p2::DistFixParam{T, F}) where T where F
    prob_equals(p1.number, p2.number)
end

function Base.:>(p1::DistFixParam{T, F}, p2::DistFixParam{T, F}) where T where F
    p1.number > p2.number
end


function Base.:+(p1::DistFixParam{T, F}, p2::DistFixParam{T, F}) where T where F
    # @assert typeof(p1) == typeof(p2)
    ans = p1.number + p2.number
    DistFixParam{T, F}(p1.mgr, ans[1]), ans[2]
end

function Base.:/(p1::DistFixParam{T, F}, p2::DistFixParam{T, F}) where T where F
    # @assert typeof(p1) == typeof(p2)
    ans = p1.number / p2.number
    ans[1], ans[2]
end

function Base.:-(p1::DistFixParam{T, F}, p2::DistFixParam{T, F}) where T where F
    # @assert typeof(p1) == typeof(p2)
    ans = p1.number - p2.number
    DistFixParam{T, F}(p1.mgr, ans[1]), ans[2]
end

function infer(d::DistFixParam{T, F}) where T where F
    point = F
    mb = length(d.number.bits)
    ans = Vector(undef, 2^mb)
    non_zero_index = 0
    for i=0:2^mb - 1
        a = infer(prob_equals(d.number, i))
        if !(a ≈ 0)
            non_zero_index = i+1
        end
        ans[i + 1] = (i/2^point, a)
    end
    @show sum(map(a -> a[2], ans))
    @assert sum(map(a -> a[2], ans)) ≈ 1.0
    ans
end

# function DistFixParam{a::Int}(b::Vector)
#     DistFixParam{a}(b[1].mgr, DistInt(b))
# end

function condinfer(d::DistFixParam{T, F}, b::DistBool) where T where F
    point = F
    mb = T
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

bools(x::DistFixParam) = bools(x.number)

# bools(i::DistFixParam) = i.number.bits