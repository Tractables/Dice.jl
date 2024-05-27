using Dates
include("benchmarks.jl")

function main()
    for (lr, samples_per_batch) in Base.product(
        [0.0001, 0.0003, 0.001, 0.003, 0.01, 0.03, 0.1, 0.3, 1.],
        [100, 1000, 10000],
    )
        test(samples_per_batch, lr)
    end
end

function test(samples_per_batch, lr)
    SEED = 0

    out_dir = "tmp/out_dir$(Dates.format(now(), dateformat"yyyy-mm-ddTHH_MM_SS"))-lr$(lr)-spb$(samples_per_batch)"
    println(out_dir)
    mkdir(out_dir)

    log_path = "tmp/log"
    rs = RunState(Valuation(), Dict{String,ADNode}(), open(log_path, "w"), out_dir, MersenneTwister(SEED), nothing)

    v = flip(register_weight!(rs, "v"; random_value=true))

    curve = []
    dists = []

    for epoch in 1:1000
        samples = with_concrete_ad_flips(rs.var_vals, v) do
            [sample_as_dist(rs.rng, Valuation(), v) for _ in 1:samples_per_batch]
        end

        loss = sum(
            LogPr(prob_equals(v, sample))
            for sample in samples
        )
        l = Dice.LogPrExpander(WMC(BDDCompiler(Dice.bool_roots([loss]))))
        loss = Dice.expand_logprs(l, loss) / samples_per_batch
        vals, derivs = differentiate(
            rs.var_vals,
            Derivs(loss => lr)
        )
        push!(curve, vals[loss])
        d = pr_mixed(rs.var_vals)(v)
        push!(dists, [d[false], d[true]])

        if isinf(vals[loss]) || isnan(vals[loss])
            break
        end

        for (adnode, d) in derivs
            if adnode isa Var
                rs.var_vals[adnode] -= d
            end
        end
    end

    save_learning_curve(rs.out_dir, curve, "loss.csv")
    save_areaplot(joinpath(rs.out_dir, "dist.svg"), dists)
end

main()