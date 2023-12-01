using Dice
using DelimitedFiles
using BenchmarkTools
using Plots

obs_bdd = Vector(undef, 3)
for j in 1:3
    cur = Vector(undef, 13)
    io = open(string("./benchmarks/gamma/nodes_obs_"*string(j)*".txt"), "a")
    for i in 2:14
        DFiP = DistFix{i+1, i}
        t = @dice unit_gamma(DFiP, j, -2.0)
        n = num_nodes(reduce(&, t.observations) & reduce(&, t.returnvalue.number.number.bits[3:i+1]) & !t.returnvalue.number.number.bits[2])
        @show i, n
        writedlm(io, [i n], ",")
        cur[i-1] = n  
    end
    close(io)
    obs_bdd[j] = cur
    plot([i for i in 2:14], cur)
    savefig("nodes_obs_lsb_"*string(j)*".png")
end

obs_bdd = Vector(undef, 3)
for j in 1:3
    io = open(string("./benchmarks/gamma/nodes_obs_"*string(j)*".txt"), "a")
    cur = readdlm(string("./benchmarks/gamma/nodes_obs_"*string(j)*".txt"), ',', Int)
    obs_bdd[j] = cur[15:28]
end
plot([i for i in 1:14], obs_bdd, labels=["gamma(2, 1)" "gamma(3, 1)" "gamma(4, 1)"], legend=:topleft, xlabel="Bits", ylabel="BDD size", title="Size of observation BDDs", line = (:solid), label=false, linewidth=5, xguidefontsize=30, xtickfontsize=15, yguidefontsize=30, ytickfontsize=15)
savefig("linear_scaling.pdf")