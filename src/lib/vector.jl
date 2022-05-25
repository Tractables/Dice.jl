# Vectors
export DistVector, prob_append, prob_extend

struct DistVector{T} <: Dist{Vector} where T <: Dist
    mgr
    contents::Vector{T}
    len::DistInt
end

function DistVector{T}(mgr) where T <: Dist
    DistVector(mgr, Vector{T}(), DistInt(mgr, 0))
end

function DistVector{T}(mgr, contents::Vector{T}) where T <: Dist
    DistVector(mgr, contents, DistInt(mgr, length(contents)))
end

function DistVector(mgr, contents::Vector)
    DistVector(mgr, contents, DistInt(mgr, length(contents)))
end

function group_infer(f, d::DistVector, prior, prior_p::Float64)
    group_infer(d.len, prior, prior_p) do len, len_prior, len_p
        group_infer(d.contents[1:len], len_prior, len_p) do v, v_prior, v_p
            f(v, v_prior, v_p)
        end
    end
end

function prob_equals(x::DistVector{T}, y::DistVector{T}) where T <: Dist
    res = prob_equals(x.len, y.len)
    for i = 1:min(length(x.contents), length(y.contents))
        res = res & ((i > x.len) | prob_equals(x.contents[i], y.contents[i]))
    end
    res
end

prob_equals(x::DistVector{T}, y::Vector{T}) where T <: Dist =
    prob_equals(x, DistVector(x.mgr, y))

prob_equals(x::Vector{T}, y::DistVector{T}) where T <: Dist =
    prob_equals(y, x)

function ifelse(cond::DistBool, then::DistVector{T}, elze::DistVector{T})::DistVector{T} where T <: Dist
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
    DistVector(cond.mgr, v, ifelse(cond, then.len, elze.len))
end

function prob_append(d::DistVector{T}, x::T)::DistVector{T} where T <: Dist
    v = Vector{T}(undef, length(d.contents) + 1)
    for i = 1:length(d.contents)
        v[i] = ifelse(prob_equals(d.len, i-1), x, d.contents[i])
    end
    v[length(d.contents) + 1] = x
    DistVector(d.mgr, v, safe_inc(d.len))
end

# Divide-and-conquer getindex
function Base.getindex(d::DistVector{T}, idx::DistInt)::Tuple{T, DistBool} where T <: Dist
    function helper(i, v)
        if v >= length(d.contents)
            return last(d.contents), (idx > d.len) | prob_equals(idx, 0)
        end
        if i > length(idx.bits)
            return if v == 0
                last(d.contents), DistBool(d.mgr, true)
            else
                d.contents[v], (idx > d.len) | prob_equals(idx, 0)
            end
        end
        ifelse(idx.bits[i], helper(i+1, v+2^(i-1)), helper(i+1, v))
    end
    return helper(1, 0)
end

function Base.getindex(d::DistVector{T}, idx::Int)::Tuple{T, DistBool} where T <: Dist
    if idx < 1 || idx > length(d.contents)
        last(d.contents), DistBool(d.mgr, true)
    else
        d.contents[idx], (idx > d.len) | prob_equals(idx, 0)
    end
end

function prob_setindex(d::DistVector{T}, idx::DistInt, x::T)::Tuple{DistVector{T}, DistBool} where T <: Dist
    contents = Vector{T}(undef, length(d.contents))
    for i = 1:length(contents)
        contents[i] = ifelse(prob_equals(idx, i), x, d.contents[i])
    end
    DistVector(d.mgr, contents, d.len), (idx > d.len) | prob_equals(idx, 0)
end

function prob_extend(u::DistVector{T}, v::DistVector{T})::DistVector{T} where T <: Dist
    if length(v.contents) == 0
        return u
    end
    len = safe_add(u.len, v.len)
    contents = Vector{T}(undef, length(u.contents) + length(v.contents))
    for i = 1:length(contents)
        if i <= length(u.contents)
            a = v[(i - u.len)[1]]
            contents[i] = ifelse(u.len > (i - 1), u.contents[i], v[(i - u.len)[1]][1])
        else
            # Subtraction could overflow, but we don't care - accessing chars beyond len is UB
            contents[i] = v[(i - u.len)[1]][1]
        end
    end
    DistVector(u.mgr, contents, len)
end

prob_extend(s::DistVector{T}, t::Vector{T}) where T <: Dist =
    prob_extend(s, DistVector(s.mgr, t))
    
prob_extend(s::Vector{T}, t::DistVector{T}) where T <: Dist =
    prob_extend(DistVector(t.mgr, s), t)

bools(d::DistVector) =
    vcat(collect(Iterators.flatten(bools(c) for c in d.contents)), bools(d.len))
