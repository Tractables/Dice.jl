using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

bits = parse(Int64, ARGS[1])
pieces = parse(Int64, ARGS[2])

# bits = 3
# pieces = 8
p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFixedPoint{5+bits, bits}

t = @timed expectation(@dice begin
                x = continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
                y = continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
                m = if (x < y) y else x end
                m
end)

p = t.value

io = open(string("./benchmarks/addFun_max/results.txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)