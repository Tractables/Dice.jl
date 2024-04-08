using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

if length(ARGS) == 0
    bits = 11
else
    bits = parse(Int64, ARGS[1])
end

flag = 0

DFiP = DistFix{8+bits, bits}

ys = [1, -1, 1, -1, -1, -1, 1, 1, 1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1, 1]
xs = DFiP.([6, 8, -1, 0, 5, 1.2, -2, 9.8, 4, 12, 1, 10, 1, 2.2, -6, 9.8, 1, 1, 1, 1])

t = @timed expectation(@dice begin
            w1 = uniform(DFiP, -8.0, 8.0)
            w2 = uniform(DFiP, -8.0, 8.0)

            for (x, y) in zip(xs, ys)
                temp = x*w1 + w2
                isneg = temp < DFiP(0.0)
                if y == 1
                    observe(!isneg | (isneg & flip(1/ℯ)))
                else
                    observe(isneg | (!isneg & flip(1/ℯ)))
                end
            end
            if flag == 1
                w1
            else
                w2
            end
        end; ignore_errors=true)

p = t.value

io = open(string("./benchmarks/zeroone_w2/results_new.txt"), "a")
@show bits, p, flag, t.time
writedlm(io, [bits p flag t.time], ",")  
close(io)



