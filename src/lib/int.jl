     
# Integers
export ProbInt, add_bits, max_bits

struct ProbInt <: Dist{Vector{DistBool}}
    mgr
    # first index is least significant bit
    # most significant bits that are always false are trimmed
    bits::Vector{DistBool}
end

function ProbInt(mgr, i::Int)
    @assert i >= 0
    # num_b = num_bits(i)
    num_b = ndigits(i, base = 2)
    bits = Vector{DistBool}(undef, num_b)
    for bit_idx = 1:num_b
        b::Bool = i & 1
        @inbounds bits[bit_idx] = DistBool(mgr, b) 
        i = i >> 1
    end
    ProbInt(mgr, bits)
end

function ProbInt(bits::Vector)
    ProbInt(bits[1].mgr, bits)
end

max_bits(i::ProbInt) =
    length(i.bits)

# @inline flip(mgr, ::Type{ProbInt}, bits::Int) =
#     ProbInt(mgr, [flip(mgr) for i = 1:bits])

function prob_equals(x::ProbInt, y::ProbInt)
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

prob_equals(x::ProbInt, y::Int) = 
    prob_equals(x, ProbInt(x.mgr, y))

prob_equals(x::Int, y::ProbInt) =
    prob_equals(y, x)

function ifelse(cond::DistBool, then::ProbInt, elze::ProbInt)
    if isvalid(cond)
        then
    elseif !issat(cond)
        elze
    else
        last_sat_bit = 0
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
        ProbInt(cond.mgr, z[1:last_sat_bit])
    end
end

#TODO: Look for optimizations here
function Base.:>(x::ProbInt, y::ProbInt)
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

# No canonical bitwidth
function Base.:+(p1::ProbInt, p2::ProbInt)
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
    ProbInt(t1.mgr, z), carry
end

Base.:+(p1::ProbInt, p2::Int) =
    p1 + ProbInt(p1.mgr, p2)

Base.:+(p1::Int, p2::ProbInt) = 
    ProbInt(p2.mgr, p1) + p2

function Base.:-(t1::ProbInt, t2::ProbInt)
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
    
    ans = ifelse(borrow, (ProbInt(z) + 1)[1], ProbInt(z))
    ans, borrow
end

function Base.:*(p1::ProbInt, p2::ProbInt)
    # p1 = ProbInt(p11.mgr, 3)
    # p2 = ProbInt(p12.mgr, 3)
    mbp1 = max_bits(p1)
    mbp2 = max_bits(p2)
    if (mbp1 > mbp2) 
        t1, t2 = p1, p2
        mb1, mb2 = mbp1, mbp2
    else
        t1, t2 = p2, p1
        mb1, mb2 = mbp2, mbp1
    end

    P = ProbInt(p1.mgr, 0)
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
        added = ifelse(t2.bits[i], ProbInt(p1.mgr, shifted_bits), ProbInt(p1.mgr, 0))
        res = (P + added)
        P = res[1]
        carry |= res[2]
    end
    P, carry
end


# function Base.:*(p1::ProbInt, p2::ProbInt)
#     p1 = ProbInt(p1.mgr, 2)
#     p2 = ProbInt(p1.mgr, 2)
#     mb1 = max_bits(p1)
#     mb2 = max_bits(p2)
#     A_bits = vcat(bools(p1), fill(DistBool(p1.mgr, false), mb2+1))
#     println(A_bits)
#     B_msb = Vector(undef, mb1)
#     for i=1:mb1
#         B_msb[i] = !p1.bits[1]
#     end
#     B_complement = ProbInt(p1.mgr, B_msb)
#     B = B_complement + 1
#     B_bits = vcat(B[1].bits, fill(DistBool(p1.mgr, false), mb2+1))

#     A = ProbInt(p1.mgr, A_bits)
#     S = ProbInt(p1.mgr, B_bits)

#     P_bits = vcat(fill(DistBool(p1.mgr, false), mb1), p2.bits, fill(DistBool(p1.mgr, false), 1))


#     false_constant = DistBool(p1.mgr, false)
#     true_constant = DistBool(p1.mgr, true)
#     zero_constant = ProbInt(p1.mgr, 0)
#     P = ProbInt(p1.mgr, P_bits)

    
#     for i = 1:mb2
#         next_P = ifelse(prob_equals(P.bits[1], P.bits[2]), zero_constant, 
#                                                     ifelse(prob_equals(P.bits[1], false_constant) & prob_equals(P.bits[2], true_constant), S, 
#                                                                                                                                         A))
#         P = (P + next_P)[1]
#         shift_P = circshift(P.bits, -1)
#         P = ProbInt(p1.mgr, shift_P)
#         P.bits[mb1 + mb2 + 1] = P.bits[mb1 + mb2]
#     end

#     ProbInt(p1.mgr, P.bits[1:mb1+mb2])
# end
    

bools(i::ProbInt) = i.bits

#No safety checks yet
function add_bits(p::ProbInt, w::Int)
    mb = max_bits(p)
    ext = Vector(undef, w)
    for i= w:-1:1
        ext[i] = DistBool(p.mgr, false)
    end
    ProbInt(p.mgr, vcat(p.bits, ext))
end
    


