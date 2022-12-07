# Vectors
export DistVector, prob_append, prob_extend, prob_startswith, prob_setindex, prob_getindex

mutable struct DistVector{T} <: Dist{Vector} where T <: Any
    contents::Vector{T}
    len::DistUInt32
end

function DistVector{T}() where T <: Any
    DistVector(Vector{T}(), DistUInt32(0))
end

function DistVector{T}(contents::Vector{T}) where T <: Any
    DistVector(contents, DistUInt32(length(contents)))
end

function DistVector(contents::Vector)
    DistVector(contents, DistUInt32(length(contents)))
end

function prob_equals(x::DistVector, y::DistVector)
    res = prob_equals(x.len, y.len)
    for i = 1:min(length(x.contents), length(y.contents))
        res = res & ((DistUInt32(i) > x.len) | prob_equals(x.contents[i], y.contents[i]))
    end
    res
end

function Base.ifelse(cond::Dist{Bool}, then::DistVector{T}, elze::DistVector{T})::DistVector{T} where T <: Any
    mb = max(length(then.contents), length(elze.contents))
    v = Vector{T}(undef, mb)
    for i = 1:mb
        if i > length(then.contents)
            v[i] = elze.contents[i]
        elseif i > length(elze.contents)
            v[i] = then.contents[i]
        else
            v[i] = ifelse(cond, then.contents[i], elze.contents[i])
        end
    end
    DistVector(v, ifelse(cond, then.len, elze.len))
end

function prob_append(d::DistVector{T}, x::T)::DistVector{T} where T <: Any
    v = Vector{T}(undef, length(d.contents) + 1)
    for i = 1:length(d.contents)
        v[i] = ifelse(prob_equals(d.len, DistUInt32(i-1)), x, d.contents[i])
    end
    v[length(d.contents) + 1] = x
    DistVector(v, d.len + DistUInt32(1))
end

# Divide-and-conquer getindex
function prob_getindex(d::DistVector, idx::DistUInt32)
    (idx < DistUInt32(1) || idx > d.len) && error("Vector out of bounds access")
    function helper(i, v)
        assert_dice()
        if i > length(idx.bits)
            if v < 1 || v > length(d.contents)
                d.contents[1]  # dummy
            else
                d.contents[v]
            end
        else
            if idx.bits[i]
                helper(i+1, v+2^(length(idx.bits) - i))
            else
                helper(i+1, v)
            end
        end
    end
    return helper(1, 0)
end

function prob_setindex(s::DistVector, idx::DistUInt32, c::Any)
    (idx < DistUInt32(1) || idx > s.len) && error("Vector out of bounds access")
    contents = collect(s.contents)
    for i = 1:length(s.contents)
        contents[i] = ifelse(prob_equals(idx, DistUInt32(i)), c, s.contents[i])
    end
    DistVector(contents, s.len)
end

function prob_setindex(s::DistVector, idx::Int, c::Any)
    (idx < 1 || DistUInt32(idx) > s.len) && error("Vector out of bounds access")
    contents = collect(s.contents)
    contents[idx] = c
    DistVector(contents, s.len)
end

function prob_extend(s::DistVector{T}, t::DistVector{T}) where T <: Any
    if isempty(s.contents)
        return t
    end
    len = s.len + t.len
    contents = Vector{T}(undef, length(s.contents) + length(t.contents))
    for i = 1:length(contents)
        contents[i] = if DistUInt32(i) <= s.len
            prob_getindex(s, DistUInt32(i))
        else
            if (DistUInt32(i) > s.len) & (DistUInt32(i) <= s.len + t.len)
                prob_getindex(t, DistUInt32(i) - s.len)
            else
                s.contents[1] # dummy value 
            end
        end
    end
    DistVector(contents, len)
end

function prob_startswith(u::DistVector, v::DistVector)
    if u.len < v.len
        return false
    end
    reduce(
        &,
        [
            (DistUInt32(i) > v.len) | prob_equals(u.contents[i], v.contents[i])
            for i in 1:length(v.contents)
        ]
    )
end

tobits(s::DistVector) =
    vcat(collect(Iterators.flatten(tobits(c) for c in s.contents)), tobits(s.len))

function frombits(s::DistVector, world)
    len = frombits(s.len, world)
    collect(frombits(c, world) for c in s.contents[1:len])
end
