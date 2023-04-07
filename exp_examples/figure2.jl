using Dice, Distributions
using Plots


function plot_gaussian(bits::Int, pieces::Int)
    DFiP = DistFixedPoint{4 + bits, bits}
    code = @dice begin 
                a = continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
                a
    end
    p = pr(code)
    p
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
        savefig("fig2_"*string(j)*".pdf")
    end
end

bits = [0, 1, 4]
gen_plots(bits)

# for j in bit_vector
    j = 7
    plot_vector = Vector(undef, j+3)
    label_string = Vector(undef, j+3)
    for i in 7:7
        p = 2^7
        a = plot_gaussian(j, p)
        plot_vector[i] = a
        label_string[i] = "p="*string(128)
    end
    plot(plot_vector[7], line = (:solid), label=false, linewidth=5, xaxis = ("x"), yaxis = ("pr(x)"), xguidefontsize=30, xtickfontsize=15, yguidefontsize=30, ytickfontsize=15)
    for i in 8:7
        plot!(plot_vector[i], line = (:solid), label = "p="*string(2^i))
    end
    savefig("fig2_"*string(j)*".pdf")
# end
