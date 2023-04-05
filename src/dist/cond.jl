export Cond, EvidMonad

struct Cond{T} <: Any where T <: Any
    x::T
    evid::AnyBool
end

function evid_bind(ma, f)
    mb = f(ma.x)
    Cond{typeof(mb).parameters[1]}(mb.x, ma.evid & mb.evid)
end

function evid_ret(x::T) where T
    Cond{T}(x, true)
end

EvidMonad = Monad(evid_bind, evid_ret)

function Base.ifelse(c::Cond{<:AnyBool}, t, e)
    EvidMonad.bind(c, c -> @dice_ite if c t else e end)
end

function Base.ifelse(b::Dist{Bool}, t::Cond{T}, e::Cond{T}) where T
    Cond{T}(ifelse(b, t.x, e.x), ifelse(b, t.evid, e.evid))
end

function pr(x::Cond{T}, args...; kwargs...) where T
    pr(x.x, args..., evidence=x.evid; kwargs...)
end

tobits(x) = vcat(tobits(x.x), tobits(x.evid))
