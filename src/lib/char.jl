# Characters
export DistChar, valid_chars

# Supported characters. Current selection is temporary
valid_chars = ['a':'z';'A':'Z';[' ',',','.','\'','"','!','?','(',')','\n']]
char_idx = Dict((c, i-1) for (i , c) in enumerate(valid_chars))

mutable struct DistChar <: Dist{Char}
    i::DistInt
end

function DistChar(c::Char)
    DistChar(DistInt(char_idx[c]))
end

function replace_helper(d::DistChar, mapping)
    DistString(replace(d.i, mapping))
end

function group_infer(f, inferer, d::DistChar, prior, prior_p::Float64)
    group_infer(inferer, d.i, prior, prior_p) do n, new_prior, p
        f(valid_chars[n+1], new_prior, p)
    end
end

prob_equals(x::DistChar, y::DistChar) =
    prob_equals(x.i, y.i)

prob_equals(x::DistChar, y::Char) =
    prob_equals(x, DistChar(y))

prob_equals(x::Char, y::DistChar) =
    prob_equals(y, x)

function ifelse(cond::DistBool, then::DistChar, elze::DistChar)
    DistChar(ifelse(cond, then.i, elze.i))
end

bools(c::DistChar) =
    bools(c.i)

Base.:>(x::DistChar, y::DistChar) = x.i > y.i

Base.:>(x::DistChar, y::Char) = x.i > DistChar(y).i

Base.:>(x::Char, y::DistChar) = DistChar(x).i > y.i

Base.:<(x::DistChar, y::DistChar) = y > x

Base.:<(x::DistChar, y::Char) = y > x

Base.:<(x::Char, y::DistChar) = y > x

Base.:(>=)(x::DistChar, y::DistChar) = !(x < y)
Base.:(>=)(x::Char, y::DistChar) = DistChar(x) >= y
Base.:(>=)(x::DistChar, y::Char) = x >= DistChar(y)

Base.:(<=)(x::DistChar, y::DistChar) = !(x > y)
Base.:(<=)(x::Char, y::DistChar) = DistChar(x) <= y
Base.:(<=)(x::DistChar, y::Char) = x <= DistChar(y)
