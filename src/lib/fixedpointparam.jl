
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

function DistFixParam{T, F}(mgr, i::Float64) where T where F
    @assert i >= 0
    @show Int(round(i*2^F))
    a =  DistInt(mgr, Int(round(i*2^F)))
    @assert length(a.bits) <= T
    ext = Vector(undef, T - length(a.bits))
    for i = 1:T - length(a.bits)
        ext[i] = DistBool(mgr, false)
    end
    DistFixParam{T, F}(vcat(a.bits, ext))
end

function DistFixParam{T, F}(i::DistFixParam{T1, F1}) where T where F where T1 where F1
    @assert F1 - F == T1 - T
    @assert F1 > F
    DistFixParam{T, F}(i.number.bits[F1 - F + 1:T1])
end

function add_bits(p::DistFixParam{T, F}, w1::Int) where T where F
    DistFixParam{T + w1, F}(p.mgr, add_bits(p.number, w1))
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
    # @show max_bits(p1.number), max_bits(p2.number)
    ans = p1.number + p2.number
    DistFixParam{T, F}(p1.mgr, ans[1]), ans[2]
end

function Base.:*(p1::DistFixParam{T, F}, p2::DistFixParam{T, F}) where T where F
    # @assert typeof(p1) == typeof(p2)
    ans = p1.number * add_bits(p2.number, T)
    # ans = p1.number * p2.number
    DistFixParam{T + T, 2*F}(p1.mgr, ans[1]), ans[2]
end

function Base.:/(p1::DistFixParam{T, F}, p2::DistFixParam{T, F}) where T where F
    # @assert typeof(p1) == typeof(p2)
    #TODO: division with decimal points
    # a = fill(DistBool(p1.mgr, false), (1, F))
    # ans = DistInt(hcat(p1.number.bits, a)) / p2.number
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
        @show i
        a = infer(prob_equals(d.number, i))
        if !(a ≈ 0)
            non_zero_index = i+1
        end
        ans[i + 1] = (i/2^point, a)
    end
    # @show sum(map(a -> a[2], ans))
    # @assert sum(map(a -> a[2], ans)) ≈ 1.0
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

function expectation(d::DistFixParam{T, F}) where T where F
    ans = expectation(d.number)
    ans/2^F
end

function expectation(d::DistFixParam{T, F}, d2::DistBool) where T where F
    ans = expectation(d.number, d2)
    ans/2^F
end

function variance(d::DistFixParam{T, F}) where T where F
    ans = variance(d.number)
    ans/2^(2F)
end

function variance(d::DistFixParam{T, F}, d2::DistBool) where T where F
    ans = variance(d.number, d2)
    ans/2^(2F)
end

bools(x::DistFixParam) = bools(x.number)

# bools(i::DistFixParam) = i.number.bits