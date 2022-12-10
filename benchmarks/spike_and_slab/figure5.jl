using Revise
using DelimitedFiles
using BenchmarkTools
using Plots
# using LinearAlgebra, ForwardDiff
# import PyPlot
# import Contour: contours, levels, level, lines, coordinates

filename = "/space/poorvagarg/.julia/dev/Dice/benchmarks/spike_and_slab/results.txt"
file_handle = open(filename)
file_lines = readlines(file_handle)
close(file_handle)

n_bits = parse(Int64, split(file_lines[length(file_lines)], ",")[1])
plot_lines = Vector(undef, n_bits+1)
for j in 1:n_bits+1
    xs = Vector(undef, j+3)
    ys = Vector(undef, j+3)
    counter = 0
    for i in 1:length(file_lines)
        cur = split(file_lines[i], ",")
        bit = parse(Int64, cur[1])
        if bit == (j-1)
            counter += 1
            xs[counter] = parse(Int64, cur[2])
            ys[counter] = parse(Float64, split(split(cur[6], " ")[4], ")")[1])
        end
    end
    plot_lines[j] = (xs, ys)
end

plot_lines

plot([Int(log2(i)) for i in plot_lines[4][1]], plot_lines[4][2], xlabel = "Log(p)", ylabel = "pr(z1 == 1)", yaxis=:log, label = "b = 11", marker = :circle, line = (:solid), legendfont=15, legend=:topright, xguidefontsize=20, xtickfontsize=15, yguidefontsize=20, left_margin=5Plots.mm, ytickfontsize=15, bottom_margin=5Plots.mm, right_margin=5Plots.mm)
for j = 5:n_bits-1
    plot!([Int(log2(i)) for i in plot_lines[j][1]], plot_lines[j][2], xaxis = "Log(p)", label = "b = "*string(j+7), marker = :circle)
end

j = 2
plot!([Int(log2(i)) for i in plot_lines[j][1]], plot_lines[j][2], xaxis = "Log(p)", yaxis = "pr(z1 == 1)", label = "b = 9", marker = :circle)
j = 3
plot!([Int(log2(i)) for i in plot_lines[j][1]], plot_lines[j][2], xaxis = "Log(p)", yaxis = "pr(z1 == 1)", label = "b = 10", marker = :circle)
j = 4
plot!([Int(log2(i)) for i in plot_lines[j][1]], plot_lines[j][2], xaxis = "Log(p)", yaxis = "pr(z1 == 1)", label = "b = 11", marker = :circle)
j = 5
plot!([Int(log2(i)) for i in plot_lines[j][1]], plot_lines[j][2], xaxis = "Log(p)", yaxis = "pr(z1 == 1)", label = "b = 12", marker = :circle)
j = 6
plot!([Int(log2(i)) for i in plot_lines[j][1]], plot_lines[j][2], xaxis = "Log(p)", yaxis = "pr(z1 == 1)", label = "b = 13", marker = :circle)
savefig("fig5.png")