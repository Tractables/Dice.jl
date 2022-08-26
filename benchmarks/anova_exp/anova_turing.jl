using Turing
using StatsPlots
using Statistics

@model function arnp(y)
    a ~ Uniform(-4, 4)
    b ~ Uniform(0, 8)

    y ~ Normal(a, b)
end;

data = 0.617007250574049

m = arnp(data)
chain = sample(m, IS(), MCMCThreads(), 1000, 1000)
Statistics.mean(chain["a"][1:1000000].data)