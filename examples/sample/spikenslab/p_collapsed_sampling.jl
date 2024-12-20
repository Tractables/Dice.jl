using Distributions
using LogExpFunctions
using DelimitedFiles
include("../ground_truth.jl")
include("../data_generation.jl")
include("../spikenslab_collapsed_sampling.jl")

n = 2 # Number of observations
p = 15 # Number of features
s = 2 # Sparsity Parameters
X, y, beta = generate_spike_slab(n, p, s)
# We don't really have a ground truth. I guess write a ground truth function for spike and slab
# mu, sigma = ground_truth_linear(X, y, [2 for _ in 1:p], 1)

bits = 15
for pj in 1:20
    _, _, bdd_size = spikenslab_collapsed_sample(bits, bits + 2, n, pj, X[:, 1:pj], y, 10)
    io = open("examples/sample/spikenslab/spikenslab_scale_with_p.txt", "a")
    @show  [bits+4 bits+2 n pj s bdd_size]
    writedlm(io, [bits+4 bits+2 n pj s bdd_size], ",")
    close(io)
end

# bits = 12
# DFiP = DistFix{9 + bits, bits}
# pieces = 4
# indicators = [flip(0.5) for _ in 1:p]
# s = rand(Bernoulli(0.5), p, bits+2)
# ws = [gaussian_bitblast_sample(DFiP, 0.0, sqrt(2.0), pieces, -8.0, 8.0, s[i, :]) for i in 1:p]
# priors = [ifelse(indicators[i], DFiP(0.0), ws[i]) for i in 1:p]
#     code = @dice begin
#                 for i in 1:n
#                     error = bitblast_linear(DFiP, Normal(0.0, 1.0), 4096, -8.0, 8.0)
#                     linear = reduce(+, map(*, DFiP.(X[i, :]), priors))
#                     observe(prob_equals(error + linear, DFiP(y[i])))         
#                 end
#             indicators[1]
#             # (linear + error).mantissa.number.bits[21]
#     end


# pr(code)
# length(code.observations)
# num_nodes(returnvalue(code))