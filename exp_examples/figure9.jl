using Dice, Distributions
using Plots
using DelimitedFiles
using BenchmarkTools

for i in 0:20
    DFiP = DistFixedPoint{4 + i, i}
    code = @dice begin
                a = continuous(DFiP, Normal(0, 1), 2^(3), -8.0, 8.0)
                a
    end

    p = @benchmark begin
                    ans = pr($code)
                    exp_ans = reduce(+, [(key*value) for (key, value) in ans])
                    # @show exp_ans
    end
    e = @benchmark expectation($code)

    io = open(string("./scratch/gaussian_exp_results.txt"), "a")
    @show i, p, e
    writedlm(io, [i p e], ",")  
    close(io)
end


# for i in 0:20
#     DFiP = DistFixedPoint{4 + i, i}
#     code = @dice begin
#                 a = continuous(DFiP, Normal(0, 1), 2^(3), -8.0, 8.0)
#                 a
#     end

#     p = @benchmark begin
#                     ans = pr($code)
#                     var_ans = reduce(+, [((key^2)*value) for (key,value) in ans]) - (reduce(+, [((key)*value) for (key,value) in ans]))^2
#     end
#     e = @benchmark variance($code)

#     io = open(string("./scratch/gaussian_var_results.txt"), "a")
#     @show i, p, e
#     writedlm(io, [i p e], ",")  
#     close(io)
# end