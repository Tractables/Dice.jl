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

function kl_divergence(p, q)
    @assert sum(p) ≈ 1.0
    @assert sum(q) ≈ 1.0
    ans = 0
    for i=1:length(p)
        if p[i] > 0
            ans += p[i] *(log(p[i]) - log(q[i]))
        end
    end
    ans
end

function gen_plots()
    gt = Vector(undef, 1024)
    d = Normal(0, 1)
    counter = 0
    for i in -8:16/1024:8-16/1024
        counter += 1
        gt[counter] = cdf(d, i+16/1024) - cdf(d, i)
    end

    plot_vector = Vector(undef, 9)
    for j in 1:9
        a = plot_gaussian(6, 2^j)
        a = sort(collect(a), by = x -> x[1])
        x = map(x -> x[2], a)
        # y = map(x -> x[2], arbeit)
        val = kl_divergence(gt, x)
        plot_vector[j] = val
    end
    return plot_vector

    # for j in bit_vector
    #     plot_vector = Vector(undef, j+3)
    #     label_string = Vector(undef, j+3)
    #     for i in 1:j + 3
    #         p = 2^i
    #         a = plot_gaussian(j, p)
    #         plot_vector[i] = a
    #         label_string[i] = "p="*string(p)
    #     end
    #     plot(plot_vector[1], line = (:solid), marker = (:circle), label = "p=2", xaxis = ("x"), yaxis = ("pr(x)"))
    #     for i in 2:j+3
    #         plot!(plot_vector[i], line = (:solid), marker = (:circle), label = "p="*string(2^i))
    #     end
    #     savefig("fig2_"*string(j)*".png")
    # end
end

gen_plots()


