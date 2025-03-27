using Revise
using Alea, Distributions
using DelimitedFiles
using BenchmarkTools


pieces = 8
io = open(string("./mini-experiments/expectation_variance/exp_var.txt"), "a")
for i = 16:20
    DFiP = DistFix{5+i, i}
    code = @dice begin
        x = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
        x
    end
    t = @benchmark expectation($code)
    exp_time = median(t).time/10^9
    t = @benchmark variance($code)
    @show median(t).time
    variance_time = median(t).time/10^9

    t = @benchmark begin
            a = pr($code)
            mean = reduce(+, [(key*value) for (key, value) in a])
            mean
    end
    @show median(t).time
    mean_time = median(t).time/10^9

    t = @benchmark begin
        a = pr($code)
        mean = reduce(+, [(key*value) for (key, value) in a])
        std_sq = reduce(+, [(key*key*value) for (key, value) in a]) - mean^2
        std_sq
    end
    @show median(t).time
    std_time = median(t).time/10^9

    writedlm(io, [i exp_time variance_time mean_time std_time], ",")
end
  
close(io)