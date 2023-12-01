using Dice
using DelimitedFiles
using BenchmarkTools
using Plots


DFiP = DistFix{23, 22}

for n_vars =10:10:100
    @show n_vars
    p = @btime pr( @dice begin
                z = [flip(0.5) for i in 1:$n_vars]
                y = reduce(&, z)
                ifelse(y, unit_gamma(DFiP, 2, -8.0) < DFiP(0.5), unit_gamma(DFiP, 2, -10.0) < DFiP(0.5))
    end)
end

p = pr(code)

num_nodes(code.returnvalue & reduce(&, code.observations))

plot(p)




for bits =2:23
    @show bits
    DFiP = DistFix{bits, bits - 1}
    p = @dice begin
                z = [flip(0.5) for i in 1:30]
                y = reduce(&, z)
                ifelse(y, unit_gamma(DFiP, 2, -8.0) < DFiP(0.5), unit_gamma(DFiP, 2, -10.0) < DFiP(0.5))
    end
    @show num_nodes(p.returnvalue & reduce(&, p.observations))
end

# & and | or for non short circuit behaviour