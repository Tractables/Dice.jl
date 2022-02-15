
#Signed Integers in 2's complement
export DistSignedInt

struct DistSignedInt
    mgr
    # sign::DistBool
    number::DistInt
end

function DistSignedInt(b::DistInt)
    DistSignedInt(b.mgr, b)
end

function prob_equals(x::DistSignedInt, y::DistSignedInt)
    mbx = max_bits(x.number)
    mby = max_bits(y.number)
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
        # println(i)
        eq &= prob_equals(x.number.bits[i], y.number.bits[i])
        !issat(eq) && return eq
    end
    eq
end

function infer(d::DistSignedInt)
    mb = max_bits(d.number)
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
        ans[i - 2^(mb-1) + 1] = (i-2^mb, a)
    end

    println(start_index)

    for i=0:2^(mb-1) - 1
        a = infer(prob_equals(d.number, i))
        if !(a ≈ 0)
            non_zero_index = i+1
        end
        # if (start_index == 0 && !(a ≈ 0))
        #     start_index = i+1
        # end
        ans[i + 2^(mb-1) + 1] = (i, a)
    end

    println(start_index)
    println(non_zero_index)

    ans
end


