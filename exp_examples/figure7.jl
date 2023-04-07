using Dice, Distributions
using Plots

a = readdlm("/space/poorvagarg/.julia/dev/Dice/scratch/clt_results.txt")

x = Vector(undef, 11)
y = Vector(undef, 11)
annot = Vector(undef, 11)
for i in 1:11
    # i = 1
    cur = split(a[i], ",")
    x[i] = parse(Float64, cur[4])
    y[i] = parse(Float64, cur[3])
    annot[i] = Int64(parse(Float64, cur[1]))
end

plot(x, y, marker=:circle, xaxis=:log, yaxis=:log)
for i =1:11
    annotate!(x[i], y[i], annot[i])
end
annotate!(x[1], y[1], annot[1])