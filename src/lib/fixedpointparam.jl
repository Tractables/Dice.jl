
export DistFixParam

struct DistFixParam{T, F} <: Dist{Int}
    mgr
    number::DistInt
end

function DistFixParam{T, F}(b::Vector) where T where F
    # @assert length(b) == T
    DistFixParam{T, F}(b[1].mgr, DistInt(b))
end

function DistFixParam{T, F}(mgr, i::Int) where T where F
    @assert i >= 0
    DistFixParam{T, F}(mgr, DistInt(mgr, i))
end

function ifelse(cond::DistBool, then::DistFixParam{T, F}, elze::DistFixParam{T, F}) where T where F
    DistFixParam{T, F}(cond.mgr, ifelse(cond, then.number, elze.number))
end


function Base.:+(p1::DistFixParam{T, F}, p2::DistFixParam{T, F}) where T where F
    # @assert typeof(p1) == typeof(p2)
    ans = p1.number + p2.number
    DistFixParam{T, F}(p1.mgr, ans[1]), ans[2]
end

function Base.:-(p1::DistFixParam{T, F}, p2::DistFixParam{T, F}) where T where F
    # @assert typeof(p1) == typeof(p2)
    ans = p1.number - p2.number
    DistFixParam{T, F}(p1.mgr, ans[1]), ans[2]
end

function infer(d::DistFixParam{T, F}) where T where F
    point = F
    mb = T
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

# function DistFixParam{a::Int}(b::Vector)
#     DistFixParam{a}(b[1].mgr, DistInt(b))
# end
