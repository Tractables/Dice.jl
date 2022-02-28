
export DistFixParam

struct DistFixParam{a} <: Dist{Int}
    mgr
    number::DistInt
end

function DistFixParam{W}(b::Vector) where W
    DistFixParam{W}(b[1].mgr, DistInt(b))
end

function DistFixParam{W}(mgr, i::Float64) where W
    @assert i >= 0
    @assert i%(1/2^W) == 0.0 
    i_proxy = i * 2^W
    DistFixParam{W}(mgr, DistInt(mgr, i_proxy))
end


function Base.:+(p1::DistFixParam{W}, p2::DistFixParam{W}) where W
    # @assert typeof(p1) == typeof(p2)
    ans = p1.number + p2.number
    DistFixParam{W}(p1.mgr, ans[1]), ans[2]
end

# function DistFixParam{a::Int}(b::Vector)
#     DistFixParam{a}(b[1].mgr, DistInt(b))
# end
