using Dice
using Plots

f(beta, i) = 1/(1 + exp(beta/2^i))


function bitshift(x::DistUInt{T}, i::Int) where T
    v = fill(false, i)
    DistUInt{T}(vcat(x.bits[i + 1: T], v))
end

bitwidth = 8
final = Vector(undef, bitwidth+1)
code= @dice begin
    x = DistUInt{3*bitwidth}(vcat(fill(false, 2*bitwidth), [flip(f(0, i)) for i in 1:bitwidth]))
    u = DistUInt{3*bitwidth}(vcat(fill(false, bitwidth), [flip(f(10, i)) for i in 1:2*bitwidth]))
    final[1] = DistUInt{3*bitwidth}(0)
    mux = uniform(DistUInt{Int(log2(bitwidth))})
    for i = bitwidth-1:-1:0
        final[bitwidth+1-i] = ifelse(prob_equals(mux, DistUInt{Int(log2(bitwidth))}(i)),
        ifelse(x.bits[3*bitwidth-i], bitshift(x, i+Int(log2(bitwidth))), DistUInt{3*bitwidth}(0)),
        final[bitwidth-i])
    end
    z = final[bitwidth+1]
    observe(u < z)
    # observe(z > DistUInt{3*bitwidth}(0))
    # observe(x < DistUInt{3*bitwidth}(128))
    x
end     

l = pr(code)
logl = Dict((a, log(b)) for (a, b) in l)
plot(l)
plot(logl)

savefig("unif-unif.png")

expectation(code)


u = DistUInt{10}(vcat(fill(false, 2), [flip(f(-10, i)) for i in 1:8]))


savefig("unif-unif.png")



expectation(x*x)
pr(code)
expectation(code)

x.bits[]