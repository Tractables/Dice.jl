using Dice
using Plots
# using StatsPlots
function dist_binomial(width, p)
    n = 2^width - 1
    Dict(
        k => binomial(n, k) * p^k * (1 - p)^(n - k)
        for k in 0:n
    )
end

function dist_uniform(width)
    n = 2^width - 1
    Dict(
        k => 1 / (n + 1)
        for k in 0:n
    )
end


for width in [3]
    for (title, target_dist) in [
        ("Uniform 0 to $(2^width-1)", dist_uniform(width))
        ("Binomial ($(2^width-1)) trials, p=0.1", dist_binomial(width, 0.1))
    ]
        vars = [Var("var$(i)_psp") for i in 0:width-1]
        int = DistUInt{width}([flip(sigmoid(x)) for x in vars])

        # Weighted training
        wt_var_to_vals = Valuation(x => 0 for x in vars)
        train_pr!(
            wt_var_to_vals,
            mle_loss([
                BoolToMax(
                    prob_equals(int, DistUInt{width}(i)),
                    weight=target_dist[i]
                )
                for i in 0:2^width-1
            ]),
            epochs=2000,
            learning_rate=0.003
        )
        wt_dist = pr(int, flip_pr_resolver=valuation_to_flip_pr_resolver(wt_var_to_vals))

        # KL divergence minimization
        kl_var_to_vals = Valuation(x => 0 for x in vars)
        train_pr!(
            kl_var_to_vals,
            kl_divergence(
                target_dist,
                int,
                Set([i => DistUInt{width}(i) for i in 0:2^width-1])
            ),
            epochs=2000,
            learning_rate=0.003
        )
        kl_dist = pr(int, flip_pr_resolver=valuation_to_flip_pr_resolver(kl_var_to_vals))

        # Counting
        counting_prs = [
            sum(p for (x, p) in target_dist if x & 2^i > 0)
            for i in 0:width-1
        ]
        counting_int = DistUInt{width}(map(flip, counting_prs))
        counting_dist = pr(counting_int)

        columns = [
            "wt" => wt_dist
            "kl" => kl_dist
            "counting" => counting_dist
            "target" => target_dist
        ]
        col_names, col_dists = zip(columns...)
        println(title)
        println("\t" * join(col_names, '\t'))
        for k in 0:2^width-1
            println("$(k)\t" * join(getindex.(col_dists, k), '\t'))
        end
        println()
    end
end