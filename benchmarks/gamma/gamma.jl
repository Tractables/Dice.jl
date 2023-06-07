using Dice
using DelimitedFiles
using BenchmarkTools

io = open(string("./benchmarks/gamma/bit.txt"), "a")
for i in 1:15
    DFiP = DistFixedPoint{i+1, i}
    t = @dice unit_gamma(DFiP, 2, -2.0)
    n = num_nodes(reduce(&, t.observations))
    @show i, n
    # writedlm(io, [i t], ",")  
end
# close(io)

io = open(string("./benchmarks/gamma/bit3.txt"), "a")
for i in 1:15
    DFiP = DistFixedPoint{i+1, i}
    t = @btime expectation(@dice unit_gamma($DFiP, 3, -2.0))
    @show t
    writedlm(io, [i t], ",")  
end
close(io)

io = open(string("./benchmarks/gamma/alpha.txt"), "a")
DFiP = DistFixedPoint{5, 4}
for i in 1:10
    t = @timed expectation(@dice unit_gamma(DFiP, i, -2.0))
    @show t.time
    writedlm(io, [i t.time], ",")
end
close(io)

a = @dice unit_gamma(DFiP, 4, -2.0) 

pr(a.observations[3])
num_nodes(a.returnvalue)
num_nodes(a.observations)

pr(a.returnvalue.number.number.bits[6])

io = open(string("./benchmarks/gamma/and.txt"), "a")
for i in 1:14
    t = @timed final =  pr(reduce(&, a.observations[1:i]))
    @show t.time
    writedlm(io, [i, t.time], ",")

end

close(io)

u1 = unit_exponential(DFiP, -2.0)
u2 = uniform(DFiP, 0.0, 1.0)
pr(u2 < u1)

io = open(string("./benchmarks/gamma/and2.txt"), "a")
for i in 1:15
    DFiP = DistFixedPoint{i+1, i}
    t = @dice unit_gamma(DFiP, 2, -2.0)
    l = @timed(pr(reduce(&, t.observations)))
    @show l.time
    writedlm(io, [i l.time], ",")  
end
close(io)

io = open(string("./benchmarks/gamma/and3.txt"), "a")
for i in 1:15
    DFiP = DistFixedPoint{i+1, i}
    t = @dice unit_gamma(DFiP, 3, -2.0)
    l = @timed(pr(reduce(&, t.observations)))
    @show l.time
    writedlm(io, [i l.time], ",")  
end
close(io)


