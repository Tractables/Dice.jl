# Strings
export DistString, prob_setindex

mutable struct DistString <: Dist{String}
    chars::Vector{DistChar}
    len::DistUInt32
end

function DistString(s::String)
    DistString([DistChar(c) for c in s], DistUInt32(length(s)))
end

function prob_equals(x::DistString, y::DistString)
    res = prob_equals(x.len, y.len)
    for i = 1:min(length(x.chars), length(y.chars))
        res = res & ((DistUInt32(i) > x.len) | prob_equals(x.chars[i], y.chars[i]))
    end
    res
end

prob_equals(x::DistString, y::String) =
    prob_equals(x, DistString(y))

prob_equals(x::String, y::DistString) =
    prob_equals(y, x)

function Base.ifelse(cond::Dist{Bool}, then::DistString, elze::DistString)
    mb = max(length(then.chars), length(elze.chars))
    chars = Vector(undef, mb)
    for i = 1:mb
        if i > length(then.chars)
            chars[i] = elze.chars[i]
        elseif i > length(elze.chars)
            chars[i] = then.chars[i]
        else
            chars[i] = ifelse(cond, then.chars[i], elze.chars[i])
        end
    end
    DistString(chars, ifelse(cond, then.len, elze.len))
end

function Base.:+(s::DistString, c::DistChar)
    chars = Vector(undef, length(s.chars) + 1)
    for i = 1:length(s.chars)
        chars[i] = ifelse(prob_equals(s.len, DistUInt32(i-1)), c, s.chars[i])
    end
    chars[length(s.chars) + 1] = c
    DistString(chars, s.len + DistUInt32(1))
end

Base.:+(s::DistString, c::Char) =
    s + DistChar(c)

# Divide-and-conquer getindex
function Base.getindex(d::DistString, idx::DistUInt32)
    (idx < DistUInt32(1) || idx > d.len) && error("String out of bounds access")
    function helper(i, v)
        if i > length(idx.bits)
            d.chars[v]
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

function Base.getindex(s::DistString, idx::Int)
    (idx < 1 || DistUInt32(idx) > s.len) && error("String out of bounds access")
    s.chars[idx]
end

function prob_setindex(s::DistString, idx::DistUInt32, c::DistChar)
    (idx < DistUInt32(1) || idx > s.len) && error("String out of bounds access")
    chars = collect(s.chars)
    for i = 1:length(s.chars)
        chars[i] = ifelse(prob_equals(idx, DistUInt32(i)), c, s.chars[i])
    end
    DistString(chars, s.len)
end

function prob_setindex(s::DistString, idx::Int, c::DistChar)
    (idx < 1 || DistUInt32(idx) > s.len) && error("String out of bounds access")
    chars = collect(s.chars)
    chars[idx] = c
    DistString(chars, s.len)
end

function prob_setindex(s::DistString, idx, c::Char)
    prob_setindex(s, idx, DistChar(c))
end

function Base.:+(s::DistString, t::DistString)
    len = s.len + t.len
    chars = Vector(undef, length(s.chars) + length(t.chars))
    for i = 1:length(chars)
        chars[i] = if DistUInt32(i) <= s.len
            s[i]
        else
            if DistUInt32(i) <= s.len + t.len
                t[DistUInt32(i) - s.len]
            else
                DistChar('x')
            end
        end
    end
    DistString(chars, len)
end

Base.:+(s::DistString, t::String) =
    s + DistString(t)

Base.:+(s::String, t::DistString) =
    DistString(s) + t

function Base.:>(s::DistString, t::DistString)
    for i_ in 1:max(length(s.chars), length(t.chars))
        i = DistUInt32(i_)
        if i > s.len
            return false
        end
        if i > t.len
            return true
        end
        if s[i] < t[i]
            return false
        end
        if s[i] > t[i]
            return true
        end
    end
    return false
end

Base.:>(x::DistString, y::String) = x > DistString(y)

Base.:>(x::String, y::DistString) = DistString(x) > y

Base.:<(x::DistString, y::DistString) = y > x

Base.:<(x::String, y::DistString) = y > x

Base.:<(x::DistString, y::String) = y > x

Base.:(>=)(x::DistString, y::DistString) = !(x < y)
Base.:(>=)(x::String, y::DistString) = DistString(x) >= y
Base.:(>=)(x::DistString, y::String) = x >= DistString(y)

Base.:(<=)(x::DistString, y::DistString) = !(x > y)
Base.:(<=)(x::String, y::DistString) = DistString(x) <= y
Base.:(<=)(x::DistString, y::String) = x <= DistString(y)

tobits(s::DistString) =
    vcat(collect(Iterators.flatten(tobits(c) for c in s.chars)), tobits(s.len))

function frombits(s::DistString, world)
    len = frombits(s.len, world)
    join(frombits(c, world) for c in s.chars[1:len])
end
