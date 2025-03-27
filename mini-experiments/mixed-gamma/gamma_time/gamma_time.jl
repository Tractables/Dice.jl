using Alea
using DelimitedFiles
using BenchmarkTools
using Plots

# We demonstrate following small experiments for mixed-gamma densities
# Scaling for time for accepting formula

# recording time
max_bits = 14
obs_bdd = Vector(undef, 3)
for j in 1:3
    cur = Vector(undef, max_bits)
    io = open(string("./mini-experiments/mixed-gamma/gamma_time_"*string(j)*".txt"), "a")
    for i in 1:max_bits
        DFiP = DistFix{i+1, i}
        t = @timed expectation(@dice unit_gamma(DFiP, j, -2.0))
        @show i, t.time
        writedlm(io, [i t.time], ",")
        cur[i] = t.time
    end
    close(io)
end

# plotting time
gamma_time = Vector(undef, 3)
for j in 1:3
    io = open(string("./mini-experiments/mixed-gamma/gamma_time_"*string(j)*".txt"), "a")
    cur = readdlm(string("./mini-experiments/mixed-gamma/gamma_time_"*string(j)*".txt"), ',', Float64)
    gamma_time[j] = cur[max_bits+1:2*max_bits]
end
plot([i for i in 1:14], gamma_time, labels=["gamma(2, 2)" "gamma(3, 2)" "gamma(4, 2)"], legend=:topleft, xlabel="Bits", ylabel="BDD size", title="Size of observation BDDs", line = (:solid), label=false, linewidth=5, xguidefontsize=30, xtickfontsize=15, yguidefontsize=30, ytickfontsize=15, yaxis=:log)
savefig("./mini-experiments/mixed-gamma/gamma_time.png")
