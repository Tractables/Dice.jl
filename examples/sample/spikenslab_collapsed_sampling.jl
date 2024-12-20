using Dice
using Random
using Distributions

function spikenslab_sample(bits, n, p, X, y, s::Matrix{Bool})
    DFiP = DistFix{9 + bits, bits}
    pieces = 2^(bits+4 - size(s)[2])
    @show pieces
    @assert size(s)[1] == p
    
    # @show DFiP, size(s)[2]
    indicators = [flip(0.5) for _ in 1:p]
    ws = [gaussian_bitblast_sample(DFiP, 0.0, sqrt(2.0), pieces, -8.0, 8.0, s[i, :]) for i in 1:p]
    priors = [ifelse(indicators[i], DFiP(0.0), ws[i]) for i in 1:p]
    code = @dice begin
                for i in 1:n
                    error = bitblast_linear(DFiP, Normal(0.0, 1.0), min(2^(4 + bits), 2048), -8.0, 8.0)
                    linear = reduce(+, map(*, DFiP.(X[i, :]), priors))
                    observe(prob_equals(error, DFiP(y[i]) - linear))         
                end
            indicators[1]
    end

    @show num_nodes(returnvalue(code))
    # @show length(observations(code))
    @show num_nodes(allobservations(code))

    inside_expectation = try expectation(code)
                         catch 
                            1.0
                         end

    prob_evidence = pr(allobservations(code))[true]
    return inside_expectation, prob_evidence, num_nodes(allobservations(code))
end

function spikenslab_collapsed_sample(total_bits, bits_sampled, n, p, X, y, NSAMPLES)
    samples = rand(Bernoulli(0.5), NSAMPLES, p, bits_sampled)
    samples = map(x -> if x == 1 true else false end, samples)
    
    mean = [spikenslab_sample(total_bits, n, p, X, y, samples[i, :, :]) for i in 1:NSAMPLES]
    num = sum(map(x -> x[1]*x[2], mean))
    den = sum(map(x -> x[2], mean))
    count = sum(map(x -> x[2] == 0.0, mean))
    @show num, den
    bdd_size = sum(map(x -> x[3], mean))/NSAMPLES
    sampled_expectation = num/den
    return sampled_expectation, count, bdd_size
end