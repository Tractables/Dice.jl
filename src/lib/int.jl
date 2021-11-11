     
# Integers

struct ProbInt <: Dist
    mgr
    # first index is least significant bit
    # most significant bits that are always false are trimmed
    bits::Vector{DistBool}
end

function ProbInt(mgr, i::Int)
    get!(mgr.int_cache, i) do
        @assert i >= 0
        num_b = num_bits(i)
        bits = Vector{DistBool}(undef, num_b)
        for bit_idx = 1:num_b
            b::Bool = i & 1
            @inbounds bits[bit_idx] = DistBool(mgr, b) 
            i = i >> 1
        end
        ProbInt(mgr, bits)
    end
end

function ProbInt(bits::Vector)
    ProbInt(bits[1].mgr, bits)
end

max_bits(i::ProbInt) =
    length(i.bits)

@inline flip(mgr, ::Type{ProbInt}, bits::Int) =
    ProbInt(mgr, [flip(mgr) for i = 1:bits])

function prob_equals(x::ProbInt, y::ProbInt)
    cache = x.mgr.equals_cache
    get!(cache, (x.bits, y.bits)) do
        shared = min(max_bits(x), max_bits(y))
        eq = true_constant(x.mgr)
        for i=max_bits(x):-1:shared+1
            eq &= !(x.bits[i])
            !issat(eq) && return eq
        end
        for i=max_bits(y):-1:shared+1
            eq &= !(y.bits[i])
            !issat(eq) && return eq
        end
        for i=shared:-1:1
            eq &= prob_equals(x.bits[i], y.bits[i])
            !issat(eq) && return eq
        end
        eq
    end
end

function ite(cond::DistBool, then::ProbInt, elze::ProbInt)
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
                ite(cond, then.bits[i], elze.bits[i])
            end
            if issat(z[i])
                last_sat_bit = i
            end
        end
        ProbInt(cond.mgr, z[1:last_sat_bit])
    end
end

bools(i::ProbInt) = i.bits

