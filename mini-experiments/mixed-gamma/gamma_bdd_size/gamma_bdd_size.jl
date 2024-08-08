using Dice
using DelimitedFiles
using BenchmarkTools
using Plots

# We demonstrate following small experiments for mixed-gamma densities
# Scaling for OBDD size for accepting formula

# recording BDD sizes
max_bits = 14
obs_bdd = Vector(undef, 3)
for j in 1:3
    cur = Vector(undef, max_bits)
    io = open(string("./mini-experiments/mixed-gamma/nodes_obs_"*string(j)*".txt"), "a")
    for i in 1:max_bits
        DFiP = DistFix{i+1, i}
        t = @dice unit_gamma(DFiP, j, -2.0)
        n = num_nodes(reduce(&, t.observations))
        @show i, n
        writedlm(io, [i n], ",")
        cur[i] = n  
    end
    close(io)
end

# plotting BDD sizes
obs_bdd = Vector(undef, 3)
for j in 1:3
    io = open(string("./mini-experiments/mixed-gamma/nodes_obs_"*string(j)*".txt"), "a")
    cur = readdlm(string("./mini-experiments/mixed-gamma/nodes_obs_"*string(j)*".txt"), ',', Int)
    obs_bdd[j] = cur[15:28]
end
plot([i for i in 1:14], obs_bdd, labels=["gamma(2, 2)" "gamma(3, 2)" "gamma(4, 2)"], legend=:topleft, xlabel="Bits", ylabel="BDD size", title="Size of observation BDDs", line = (:solid), label=false, linewidth=5, xguidefontsize=30, xtickfontsize=15, yguidefontsize=30, ytickfontsize=15, yaxis=:log)
savefig("./mini-experiments/mixed-gamma/node_obs.png")
