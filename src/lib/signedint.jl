
#Signed Integers in 2's complement
export DistSigned, isneg, trunc

struct DistSigned{T, F} <: Dist{Int}
    mgr
    number::DistInt
end

function DistSigned{T, F}(b::DistInt) where T where F
    DistSigned{T, F}(b.mgr, b)
end

function DistSigned{T, F}(b::Vector) where T where F
    ext = Vector(undef, T - length(b))
    for i = 1:T-length(b)
        ext[i] = DistBool(b[1].mgr, false)
    end

    DistSigned{T, F}(b[1].mgr, DistInt(vcat(b, ext)))
end

function DistSigned{T, F}(mgr, i::Float64) where T where F
    @assert i*2^F < 2^(T-1)
    @assert i*2^F >= - (2^(T-1))
    # @show Int(floor(i*2^F))
    if (i >= 0)
        # @show i, Int(floor(i*2^F))/2^F
        a = DistInt(mgr, Int(floor(i*2^F)))
    else
        # @show i, Int(floor(2^T + i*2^F))
        a = DistInt(mgr, Int(floor(2^T + i*2^F)))
    end
    # @show length(a.bits)
    DistSigned{T, F}(mgr, add_bits(a, T - length(a.bits)))
end

function DistSigned{T, F}(mgr, i::Float64, a::Int) where T where F
    @assert i*2^F < 2^(T-1)
    @assert i*2^F >= - (2^(T-1))
    # @show Int(floor(i*2^F))
    if (i >= 0)
        # @show i, Int(floor(i*2^F))/2^F
        a = DistInt(mgr, Int(round(i*2^F)))
    else
        # @show i, Int(floor(2^T + i*2^F))
        a = DistInt(mgr, Int(round(2^T + i*2^F)))
    end
    # @show length(a.bits)
    DistSigned{T, F}(mgr, add_bits(a, T - length(a.bits)))
end

function isneg(a::DistSigned{T, F}) where T where F
    a.number.bits[T]
end

function ifelse(cond::DistBool, then::DistSigned{T, F}, elze::DistSigned{T, F}) where T where F
    DistSigned{T, F}(cond.mgr, ifelse(cond, then.number, elze.number))
end

function prob_equals(x::DistSigned{T, F}, y::DistSigned{T, F}) where T where F
    mbx = T
    mby = T
    shared = min(mbx, mby)
    eq = true
    for i=mbx:-1:shared+1
        eq &= prob_equals(x.number.bits[i], y.number.bits[shared])
        !issat(eq) && return eq
    end
    for i=mby:-1:shared+1
        eq &= prob_equals(y.number.bits[i], x.number.bits[shared])
        !issat(eq) && return eq
    end
    for i=shared:-1:1
        eq &= prob_equals(x.number.bits[i], y.number.bits[i])
        !issat(eq) && return eq
    end
    eq
end

function Base.:-(t1::DistSigned{T, F}, t2::DistSigned{T, F}) where T where F
    ans = t1.number - t2.number
    DistSigned{T, F}(t1.mgr, ans[1]), ans[2]
end

function Base.:+(p1::DistSigned{T, F}, p2::DistSigned{T, F}) where T where F
    # @assert typeof(p1) == typeof(p2)
    ans = p1.number + p2.number
    DistSigned{T, F}(p1.mgr, ans[1]), ans[2]
end

function add_bits(p::DistSigned{T, F}, w1::Int, w2::Int) where T where F
    mb = T
    ext = Vector(undef, w1)
    ext2 = Vector(undef, w2)
    for i= w1:-1:1
        ext[i] = p.number.bits[T]
    end
    for i=w2:-1:1
        ext2[i] = DistBool(p.mgr, false)
    end

    DistSigned{T + w1 + w2, F + w2}(vcat(ext2, vcat(p.number.bits, ext)))
end

function Base.:*(p1::DistSigned{T1, F1}, p2::DistSigned{T2, F2}) where T1 where F1 where T2 where F2
    # @assert typeof(p1) == typeof(p2)
    p1_n = add_bits(p1, T2, 0)
    p2_n = add_bits(p2, T1, 0)
    # @show max_bits(p1_n.number), max_bits(p2_n.number)
    ans, _ = p1_n.number * p2_n.number
    # @show max_bits(ans)
    @assert max_bits(ans) == T1 + T2
    DistSigned{T1 + T2, F1 + F2}(p1.mgr, ans)
end

function trunc(p::DistSigned{T, F}, b::Int) where T where F
    @assert b <= F
    DistSigned{T - b, F - b}(p.number.bits[b+1: T])
end

function infer(d::DistSigned{T, F}) where T where F
    mb = T
    ans = Vector(undef, 2^mb)
    non_zero_index = 0
    start_index = 0

    for i=2^(mb-1):2^mb - 1
        a = infer(prob_equals(d.number, i))
        if !(a ≈ 0)
            non_zero_index = i+1
        end
        # if (start_index == 0 && !(a ≈ 0))
        #     start_index = i+1 - 2^(mb-1)
        # end
        ans[i - 2^(mb-1) + 1] = ((i-2^mb)/2^F, a)
    end

    for i=0:2^(mb-1) - 1
        a = infer(prob_equals(d.number, i))
        if !(a ≈ 0)
            non_zero_index = i+1
        end
        # if (start_index == 0 && !(a ≈ 0))
        #     start_index = i+1
        # end
        ans[i + 2^(mb-1) + 1] = (i/2^F, a)
    end

    ans
end

function condinfer(d::DistSigned{T, F}, b::DistBool) where T where F
    mb = T
    ans = Vector(undef, 2^mb)
    non_zero_index = 0
    start_index = 0

    for i=2^(mb-1):2^mb - 1
        a = infer(Cond(prob_equals(d.number, i), b))
        if !(a ≈ 0)
            non_zero_index = i+1
        end
        # if (start_index == 0 && !(a ≈ 0))
        #     start_index = i+1 - 2^(mb-1)
        # end
        ans[i - 2^(mb-1) + 1] = ((i-2^mb)/2^F, a)
    end

    for i=0:2^(mb-1) - 1
        a = infer(Cond(prob_equals(d.number, i), b))
        if !(a ≈ 0)
            non_zero_index = i+1
        end
        # if (start_index == 0 && !(a ≈ 0))
        #     start_index = i+1
        # end
        ans[i + 2^(mb-1) + 1] = (i/2^F, a)
    end

    ans
end

bools(i::DistSigned) = bools(i.number) 

function expectation(b1::DistSigned{T, F}) where T where F
    mb = T
    @show mb
    ans = 0
    exponent = 1
    for i = 1:mb-1
        ans += exponent*expectation(b1.number.bits[i])
        exponent *= 2
    end
    ans -= exponent*expectation(b1.number.bits[mb])
    ans = ans/2^F
    return ans
end

function expectation(b1::DistSigned{T, F}, b2::DistBool) where T where F
    mb = T
    ans = 0
    exponent = 1
    for i = 1:mb-1
        ans += exponent*expectation(b1.number.bits[i], b2)
        exponent *= 2
    end
    ans -= exponent*expectation(b1.number.bits[mb], b2)
    ans = ans/2^F
    return ans
end

function variance(t1::DistSigned{T, F}) where T where F
    ans = 0
    mb = T
    b1 = t1.number
    probs = Matrix(undef, mb, mb)
    
    for i = 1:mb
        probs[i, i] = infer(b1.bits[i])
        for j = i+1:mb
            probs[i, j] = infer(b1.bits[i] & b1.bits[j])
        end
    end
    
    exponent1 = 1
    for i = 1:mb
        ans += exponent1*(probs[i, i] - probs[i, i]^2)
        exponent2 = exponent1*2
        for j = i+1:mb
            exponent2 = 2*exponent2
            bi = probs[i, i]
            bj = probs[j, j]
            bibj = probs[i, j]
            
            if j == mb
                ans -= exponent2 * (bibj - bi * bj)
            else
                ans += exponent2 * (bibj - bi * bj)
                # ans -= 2*exponent2 * (probs[i, mb] - probs[i, i] * probs[mb, mb])
            end
        end
        # @show exponent2 exponent1
        
        exponent1 = exponent1*4
    end
    return ans/2^(2F)
end

function variance(t1::DistSigned{T, F}, b2::DistBool) where T where F
    ans = 0
    mb = T
    b1 = t1.number
    probs = Matrix(undef, mb, mb)
    
    for i = 1:mb
        probs[i, i] = condinfer(b1.bits[i], b2)
        for j = i+1:mb
            probs[i, j] = condinfer(b1.bits[i] & b1.bits[j], b2)
        end
    end
    
    exponent1 = 1
    for i = 1:mb
        ans += exponent1*(probs[i, i] - probs[i, i]^2)
        exponent2 = exponent1*2
        for j = i+1:mb
            exponent2 = 2*exponent2
            bi = probs[i, i]
            bj = probs[j, j]
            bibj = probs[i, j]
            
            if j == mb
                ans -= exponent2 * (bibj - bi * bj)
            else
                ans += exponent2 * (bibj - bi * bj)
                # ans -= 2*exponent2 * (probs[i, mb] - probs[i, i] * probs[mb, mb])
            end
        end
        # @show exponent2 exponent1
        
        exponent1 = exponent1*4
    end
    return ans/2^(2F)
end


