     
# Integers
export DistInt, add_bits, max_bits

struct DistInt <: Dist{Int}
    mgr
    # first index is least significant bit
    # most significant bits that are always false are trimmed
    bits::Vector{DistBool}
end

function DistInt(mgr, i::Int)
    @assert i >= 0
    # num_b = num_bits(i)
    num_b = ndigits(i, base = 2)
    bits = Vector{DistBool}(undef, num_b)
    for bit_idx = 1:num_b
        b::Bool = i & 1
        @inbounds bits[bit_idx] = DistBool(mgr, b) 
        i = i >> 1
    end
    DistInt(mgr, bits)
end

function DistInt(bits::Vector)
    DistInt(bits[1].mgr, bits)
end

function infer(d::DistInt)
    mb = max_bits(d)
    ans = Vector(undef, 2^mb)
    non_zero_index = 0
    for i=0:2^mb - 1
        a = infer(prob_equals(d, i))
        if !(a ≈ 0)
            non_zero_index = i+1
        end
        ans[i + 1] = a
    end
    ans[1:non_zero_index]
end

max_bits(i::DistInt) =
    length(i.bits)

# @inline flip(mgr, ::Type{DistInt}, bits::Int) =
#     DistInt(mgr, [flip(mgr) for i = 1:bits])

function prob_equals(x::DistInt, y::DistInt)
    shared = min(max_bits(x), max_bits(y))
    eq = true
    for i=max_bits(x):-1:shared+1
        eq &= !(x.bits[i])
        !issat(eq) && return eq
    end
    for i=max_bits(y):-1:shared+1
        eq &= !(y.bits[i])
        !issat(eq) && return eq
    end
    for i=shared:-1:1
        # println(i)
        eq &= prob_equals(x.bits[i], y.bits[i])
        !issat(eq) && return eq
    end
    eq
end

prob_equals(x::DistInt, y::Int) = 
    prob_equals(x, DistInt(x.mgr, y))

prob_equals(x::Int, y::DistInt) =
    prob_equals(y, x)

function ifelse(cond::DistBool, then::DistInt, elze::DistInt)
    if isvalid(cond)
        then
    elseif !issat(cond)
        elze
    else
        last_sat_bit = 1
        mbthen, mbelze = max_bits(then), max_bits(elze)
        mb = max(mbthen, mbelze)
        z = Vector{DistBool}(undef, mb)
        for i=1:mb
            z[i] = if i > mbthen 
                !cond & elze.bits[i]
            elseif i > mbelze
                 cond & then.bits[i]
            else
                ifelse(cond, then.bits[i], elze.bits[i])
            end
            if issat(z[i])
                last_sat_bit = i
            end
        end
        DistInt(cond.mgr, z[1:last_sat_bit])
    end
end

#TODO: Look for optimizations here
function Base.:>(x::DistInt, y::DistInt)
    mx, my = max_bits(x), max_bits(y)
    shared = min(mx, my)
    eq = false
    prop = true
    for i=mx:-1:my+1
        prop &= !x.bits[i]
    end 
    eq |= !prop
    for i = my:-1:mx+1
        prop &= !y.bits[i]
    end
    for i=shared:-1:1    
        eq |= ifelse(prop, ifelse(x.bits[i] & !y.bits[i], true, false), false)
        prop &= prob_equals(x.bits[i], y.bits[i])
    end
    eq
end

Base.:>(x::DistInt, y::Int) = x > DistInt(x.mgr, y)

Base.:>(x::Int, y::DistInt) = DistInt(y.mgr, x) > y

# No canonical bitwidth
function Base.:+(p1::DistInt, p2::DistInt)
    last_sat_bit = 0
    mb1, mb2 = max_bits(p1), max_bits(p2)
    if (mb1 > mb2)
        t1, t2 = p1, p2
        mab, mib = mb1, mb2
    else   
        t1, t2 = p2, p1
        mab, mib = mb2, mb1
    end

    z = Vector{DistBool}(undef, mab)
    carry = false
    for i = 1:mib
        z[i] = (!t1.bits[i] & t2.bits[i]) | (t1.bits[i] & !t2.bits[i])
        z[i] = (!z[i] & carry) | (z[i] & !carry) #combine in one line or maybe add XOR too
        carry = (t1.bits[i] & t2.bits[i]) | (carry & (t1.bits[i] | t2.bits[i]))
        # if issat(z[i])
        #     last_sat_bit = i
        # end
    end
    for i = mib+1:mab
        z[i] = (!t1.bits[i] & carry) | (t1.bits[i] & !carry)
        carry = t1.bits[i] & carry
        # if issat(z[i])
        #     last_sat_bit = i
        # end
    end
    DistInt(t1.mgr, z), carry
end

Base.:+(p1::DistInt, p2::Int) =
    p1 + DistInt(p1.mgr, p2)

Base.:+(p1::Int, p2::DistInt) = 
    DistInt(p2.mgr, p1) + p2

function Base.:+(p1::Tuple{DistInt, DistBool}, p2::DistInt)
    a = p1[1] + p2
    a[1], a[2] | p1[2]
end

function Base.:+(p1::DistInt, p2::Tuple{DistInt, DistBool})
    a = p1 + p2[1]
    a[1], a[2] | p2[2]
end

function Base.:+(p2::Tuple{DistInt, DistBool}, p1::Tuple{DistInt, DistBool})
    a = p1[1] + p2[1]
    a[1], a[2] | p1[2] | p2[2]
end

function Base.:-(t1::DistInt, t2::DistInt)
    last_sat_bit = 0
    mb1, mb2 = max_bits(t1), max_bits(t2)
    mab = max(mb1, mb2)
    mib = min(mb1, mb2)

    z = Vector{DistBool}(undef, mab)
    borrow = false
    for i = 1:mib
        z[i] = ifelse(!borrow, (!t1.bits[i] & t2.bits[i]) | (t1.bits[i] & !t2.bits[i]), prob_equals(t1.bits[i], t2.bits[i]))
        borrow = ifelse(!borrow, !t1.bits[i] & t2.bits[i], !t1.bits[i] | t2.bits[i])
    end
    for i = mib+1:mb1
        z[i] = (!t1.bits[i] & borrow) | (t1.bits[i] & !borrow)
        borrow = !t1.bits[i] & borrow
    end

    for i = mib+1:mb2
        z[i] = (!t2.bits[i] & borrow) | (t2.bits[i] & !borrow)
        borrow = t2.bits[i] | borrow 
    end

    for i = 1:mab
        z[i] = ifelse(borrow, !z[i], z[i])
    end
    
    ans = ifelse(borrow, (DistInt(z) + 1)[1], DistInt(z))
    ans, borrow
end

Base.:-(p1::DistInt, p2::Int) =
    p1 - DistInt(p1.mgr, p2)

Base.:-(p1::Int, p2::DistInt) = 
    DistInt(p2.mgr, p1) - p2

function Base.:*(p1::DistInt, p2::DistInt)
    mbp1 = max_bits(p1)
    mbp2 = max_bits(p2)
    if (mbp1 > mbp2) 
        t1, t2 = p1, p2
        mb1, mb2 = mbp1, mbp2
    else
        t1, t2 = p2, p1
        mb1, mb2 = mbp2, mbp1
    end

    P = DistInt(p1.mgr, 0)
    P = add_bits(P, mb1 - 1)
    shifted_bits = t1.bits
    carry = false
    for i=1:mb2
        if (i != 1)
            carry |= ifelse(t2.bits[i], shifted_bits[mb1], false)
            println(mb1)
            println(shifted_bits)
            shifted_bits = vcat(DistBool(p1.mgr, false), shifted_bits[1:mb1 - 1])
        end
        added = ifelse(t2.bits[i], DistInt(p1.mgr, shifted_bits), DistInt(p1.mgr, 0))
        res = (P + added)
        P = res[1]
        carry |= res[2]
    end
    P, carry
end 

Base.:*(p1::DistInt, p2::Int) =
    p1 * DistInt(p1.mgr, p2)

Base.:*(p1::Int, p2::DistInt) = 
    DistInt(p2.mgr, p1) * p2

function Base.:*(p1::Tuple{DistInt, DistBool}, p2::DistInt)
    a = p1[1] * p2
    a[1], a[2] | p1[2]
end

function Base.:*(p1::DistInt, p2::Tuple{DistInt, DistBool})
    a = p1 * p2[1]
    a[1], a[2] | p2[2]
end

function Base.:*(p2::Tuple{DistInt, DistBool}, p1::Tuple{DistInt, DistBool})
    a = p1[1] * p2[1]
    a[1], a[2] | p1[2] | p2[2]
end

function Base.:/(p1::DistInt, p2::DistInt) #p1/p2
    mb1 = max_bits(p1)
    mb2 = max_bits(p2)
    p1_bits = Vector(undef, 0)
    ans = Vector(undef, 0)

    is_zero = DistBool(p1.mgr, true)
    for i=1:mb2
        is_zero &= !p2.bits[i]
    end


    for i = mb1:-1:1
        p1_proxy = DistInt(p1.mgr, p1_bits)
        p1_bits = vcat(p1.bits[i:i], ifelse(p2 > p1_proxy, p1_proxy, (p1_proxy - p2)[1]).bits)
        ans = vcat(ifelse(p2 > p1_proxy, DistBool(p1.mgr, false), DistBool(p1.mgr, true)), ans)
    end
    p1_proxy = DistInt(p1.mgr, p1_bits)
    ans = vcat(ifelse(p2 > p1_proxy, DistBool(p1.mgr, false), DistBool(p1.mgr, true)), ans)
    ifelse(is_zero, p2, DistInt(p1.mgr, ans)), is_zero
end 

function Base.:%(p1::DistInt, p2::DistInt) #p1%p2
    mb1 = max_bits(p1)
    mb2 = max_bits(p2)
    p1_bits = Vector(undef, 0)

    is_zero = DistBool(p1.mgr, true)
    for i=1:mb2
        is_zero &= !p2.bits[i]
    end

    for i = mb1:-1:1
        p1_proxy = DistInt(p1.mgr, p1_bits)
        p1_bits = vcat(p1.bits[i], ifelse(p2 > p1_proxy, p1_proxy, (p1_proxy - p2)[1]).bits)
    end
    p1_proxy = DistInt(p1.mgr, p1_bits)
    p1_bits = ifelse(p2 > p1_proxy, p1_proxy, (p1_proxy - p2)[1]).bits
    ifelse(is_zero, p2, DistInt(p1.mgr, p1_bits)), is_zero
    # DistInt(p1.mgr, p1_bits), DistBool(p1.mgr, false)
    # end
end 

bools(i::DistInt) = i.bits

#No safety checks yet
function add_bits(p::DistInt, w::Int)
    mb = max_bits(p)
    ext = Vector(undef, w)
    for i= w:-1:1
        ext[i] = DistBool(p.mgr, false)
    end
    DistInt(p.mgr, vcat(p.bits, ext))
end
    


