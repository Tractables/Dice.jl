export DistEnum

struct DistEnum <: Dist{Enum}
    enum::Type
    i::DistInt
end

function replace_helper(d::DistEnum, mapping)
    DistEnum(d.enum, replace(d.i, mapping))
end

function DistEnum(case)
    @assert typeof(case) <: Enum
    DistEnum(typeof(case), DistInt(Int(case)))
end

function group_infer(f, inferer, d::DistEnum, prior, prior_p::Float64)
    group_infer(inferer, d.i, prior, prior_p) do n, new_prior, p
        f(d.enum(n), new_prior, p)
    end
end

function prob_equals(x::DistEnum, y::DistEnum)
    @assert x.enum == y.enum
    prob_equals(x.i, y.i)
end

prob_equals(x::DistEnum, y) =
    prob_equals(x, DistEnum(x.enum, y))

prob_equals(x, y::DistEnum) =
    prob_equals(DistEnum(y.enum, x), y)

function ifelse(cond::DistBool, then::DistEnum, elze::DistEnum)
    @assert then.enum == elze.enum
    DistEnum(then.enum, ifelse(cond, then.i, elze.i))
end

bools(c::DistEnum) =
    bools(c.i)
