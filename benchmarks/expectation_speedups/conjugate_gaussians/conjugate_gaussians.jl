using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

# bits = parse(Int64, ARGS[1])
# pieces = parse(Int64, ARGS[2])
bits = 17
pieces=4096
p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFixedPoint{5 + bits, bits}

data = DFiP.([1.0, 2.0])
add_arg = true

code = (@dice begin
                a = continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
                for datapt in data
                    gaussian_observe(DFiP, pieces, -8.0, 8.0, a, 1.0, datapt, add=add_arg)
                    @show datapt
                end
                a
            end)

t1 = @benchmark begin
    temp = pr(code)
    e = reduce(+, [(key*value) for (key, value) in temp])
end

t2 = @benchmark begin
            temp = expectation(code)
            # e = reduce(+, [(key*value) for (key, value) in temp])
        end

t3 = @benchmark begin
            temp = pr(code)
            e = reduce(+, [(key*value) for (key, value) in temp])
            v = reduce(+, [(key*key*value) for (key, value) in temp]) - e^2
        end

t4 = @benchmark begin
            temp = variance(code)
            # e = reduce(+, [(key*value) for (key, value) in temp])
        end


@show "conjugate_gaussians", median(t1).time, median(t2).time, median(t3).time, median(t4).time
# p = t.value

# io = open(string("./benchmarks/conjugate_gaussians/results.txt"), "a")
# @show bits, pieces, p, t.time
# writedlm(io, [bits pieces p t.time], ",")  
# close(io)