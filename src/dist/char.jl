# Characters
export DistChar, valid_chars, char_nbits

# Supported characters. Current selection is temporary
valid_chars = ['a':'z';'A':'Z';[' ',',','.','\'','"','!','?','(',')','\n']]
char_idx = Dict((c, i-1) for (i , c) in enumerate(valid_chars))
char_nbits = ndigits(length(valid_chars), base=2)

mutable struct DistChar <: Dist{Char}
    i::DistUInt{char_nbits}
end

function DistChar(c::Char)
    DistChar(DistUInt{char_nbits}(char_idx[c]))
end

prob_equals(x::DistChar, y::DistChar) =
    prob_equals(x.i, y.i)

prob_equals(x::DistChar, y::Char) =
    prob_equals(x, DistChar(y))

prob_equals(x::Char, y::DistChar) =
    prob_equals(y, x)

function Base.ifelse(cond::Dist{Bool}, then::DistChar, elze::DistChar)
    DistChar(ifelse(cond, then.i, elze.i))
end

Base.isless(x::DistChar, y::DistChar) = isless(x.i, y.i)
Base.:(<=)(x::DistChar, y::DistChar) = !isless(y, x)
Base.:(>=)(x::DistChar, y::DistChar) = !isless(x, y)

tobits(c::DistChar) = tobits(c.i)
frombits(c::DistChar, world) = valid_chars[frombits(c.i, world) + 1]