using Revise
using Dice 
using BenchmarkTools

function unsafesubtract(x::DistUInt{W}, y::DistUInt{W}) where W
    z = Vector{AnyBool}(undef, W)
    borrow = false
    for i=W:-1:1
        z[i] = xor(x.bits[i], y.bits[i], borrow)
        borrow = ifelse(borrow, !x.bits[i] | y.bits[i], !x.bits[i] & y.bits[i])
    end
    DistUInt{W}(z)
end

function unsafemod(p1::DistUInt{W}, p2::DistUInt{W}) where W
    p1_proxy = DistUInt{W}(0)
    for i = 1:W
        p1_proxy = DistUInt{W}(vcat(p1_proxy.bits[2:W], p1.bits[i]))
        p1_proxy = ifelse(p2 > p1_proxy, p1_proxy, unsafesubtract(p1_proxy,p2))
    end
    p1_proxy
end 

function gcd(a::DistUInt{W}, b::DistUInt{W}) where W
    for _ = 1 : 1 + W ÷ log2(MathConstants.golden)
        amb = unsafemod(a, b)
        amb = ifelse(prob_equals(amb, DistUInt{W}(0)), b, amb)
        b, a = amb, b
    end
    return a
end

function uniform_interleaved(n, k; reverse=false)
    m = Matrix(undef, n+1, k)
    m[1,:] .= false
    for i=1:n
        order = reverse ? (k:-1:1) : (1:k)
        for j=order
            m[i+1,j] = flip(0.5)
        end
    end
    [mapslices(v -> DistUInt{n+1}(v), m; dims=[1])...]
end

function uniform_coprime(n) 
    DInt = DistUInt{n+1}
    b, a = uniform_interleaved(n, 2; reverse=false)
    a += DInt(1)
    b += DInt(1)
    g = gcd(a, b)
    prob_equals(g, DInt(1))
end


t = @btime begin 
             c = uniform_coprime(8)
             p = pr(c)[true]
end
# for n=1:12
#     @show n
#     code = @showtime uniform_coprime(n)
#     @show Dice.num_ir_nodes(code)
#     p = @showtime pr(code)[true]
#     @show p
#     println()
# end
