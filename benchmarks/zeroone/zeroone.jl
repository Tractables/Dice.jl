using Revise
using Dice, Distributions
using DelimitedFiles

bits = ARGS[1]

DFiP = DistFixedPoint{7+bits, bits}

w1 = uniform(DFiP, -8.0, 8.0)
w2 = uniform(DFiP, -8.0, 8.0)

ys = [1, -1, 1, -1, -1, -1, 1, 1, 1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1, 1]
xs = DFiP.([6, 8, -1, 0, 5, 1.2, -2, 9.8, 4, 12, 1, 10, 1, 2.2, -6, 9.8, 1, 1, 1, 1])

code = dice() do
            for (x, y) in zip(xs[1:1], ys[1:1])
                temp = x*w1 + w2
                isneg = temp < DFiP(0.0)

                # t = dice() do
                if y == 1
                    observe(!isneg || (isneg & flip(1/ℯ)))
                    true
                else
                    observe(isneg || (!isneg & flip(1/ℯ)))
                    false
                end
            # end
            end
            w1
        end

p = expectation(code)

io = open(string("./benchmarks/zeroone/results.txt"), "a")
@show bits, p[1.0]
writedlm(io, [bits, p[1.0]], ",")  
close(io)



