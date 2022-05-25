export DistEnum

struct DistEnum <: Dist{Enum}
    mgr
    enum::Type
    i::DistInt
end

function DistEnum(mgr, case)
    @assert typeof(case) <: Enum
    DistEnum(mgr, typeof(case), DistInt(mgr, Int(case)))
end

function group_infer(f, d::DistEnum, prior, prior_p::Float64)
    group_infer(d.i, prior, prior_p) do n, new_prior, p
        f(d.enum(n), new_prior, p)
    end
end

function prob_equals(x::DistEnum, y::DistEnum)
    @assert x.enum == y.enum
    prob_equals(x.i, y.i)
end

prob_equals(x::DistEnum, y) =
    prob_equals(x, DistEnum(x.mgr, x.enum, y))

prob_equals(x, y::DistEnum) =
    prob_equals(DistEnum(y.mgr, y.enum, x), y)

function ifelse(cond::DistBool, then::DistEnum, elze::DistEnum)
    @assert then.enum == elze.enum
    DistEnum(cond.mgr, then.enum, ifelse(cond, then.i, elze.i))
end

bools(c::DistEnum) =
    bools(c.i)
