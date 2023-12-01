using Dice
using Plots

code = @dice unit_gamma(DistFix{15, 14}, 1, -7.0)
a = pr(code)
plot(a)

plot(a, line = (:solid), label=false, linewidth=5, xaxis = ("x"), yaxis = ("pr(x)"), xguidefontsize=30, xtickfontsize=15, yguidefontsize=30, ytickfontsize=15)
savefig("fig1a"*string(14)*".pdf")