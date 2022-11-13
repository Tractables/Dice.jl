export DistEnum

mutable struct DistEnum <: Dist{Enum}
    enum::Type
    i::DistUInt32
end

function DistEnum(case)
    @assert typeof(case) <: Enum
    DistEnum(typeof(case), DistUInt32(Int(case)))
end

function prob_equals(x::DistEnum, y::DistEnum)
    @assert x.enum == y.enum
    prob_equals(x.i, y.i)
end

function Base.ifelse(cond::Dist{Bool}, then::DistEnum, elze::DistEnum)
    @assert then.enum == elze.enum
    DistEnum(then.enum, ifelse(cond, then.i, elze.i))
end

tobits(x::DistEnum) = tobits(x.i)

frombits(x::DistEnum, world) =
    x.enum(frombits(x.i, world))
