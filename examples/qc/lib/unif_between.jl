

minvalue(x::DistUInt) = frombits(x, Dict(b => false for b in tobits(x)))
maxvalue(x::DistUInt) = frombits(x, Dict(b => true for b in tobits(x)))

# Return generated value and observation
function uniform(lo::DistUInt{W}, hi::DistUInt{W}) where W
    x = uniform(DistUInt{W}, minvalue(lo), maxvalue(hi) + 1)
    x, (x >= lo) & (x <= hi)
end