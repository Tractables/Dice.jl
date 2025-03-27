using Alea, Distributions
using Plots

# Plot approximations of gaussian
function plot_gaussian(bits::Int, pieces::Int)
    DFiP = DistFix{4 + bits, bits}
    code = @dice bitblast_exponential(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
    pr(code)
end

function gen_plots(bit_vector)
    for j in bit_vector
        plot_vector = Vector(undef, j+3)
        label_string = Vector(undef, j+3)
        for i in 1:j + 3
            p = 2^i
            a = plot_gaussian(j, p)
            plot_vector[i] = a
            label_string[i] = "p="*string(p)
        end
        plot(plot_vector[1], line = (:solid), marker = (:circle), label = "p=2", xaxis = ("x"), yaxis = ("pr(x)"), legendfont=20, xguidefontsize=30, xtickfontsize=15, yguidefontsize=30, ytickfontsize=15)
        for i in 2:j+3
            plot!(plot_vector[i], line = (:solid), marker = (:circle), label = "p="*string(2^i))
        end
        savefig("mini-experiments/plot_gauss/fig_"*string(j)*".png")
    end
end

bits = [0, 1, 4, 5]
gen_plots(bits)