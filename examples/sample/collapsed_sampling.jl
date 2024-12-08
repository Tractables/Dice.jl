using Dice
using Random
using Distributions

function linear_regression_sample(bits, n, p, X, y, s::Matrix{Bool})
    DFiP = DistFix{9 + bits, bits}
    pieces = 2^(bits+5 - size(s)[2])
    @assert size(s)[1] == n+p
    
    # @show DFiP, size(s)[2]
    ws = [gaussian_bitblast_sample(DFiP, 0.0, sqrt(2.0), pieces, -16.0, 16.0, s[i, :]) for i in 1:p]
    code = @dice begin
                for i in 1:n
                    # error = bitblast_linear(DFiP, Normal(0.0, 1.0), 2^(4 + bits), -8.0, 8.0)
                    error = gaussian_bitblast_sample(DFiP, 0.0, 1.0, Int(pieces/2), -8.0, 8.0, s[i+p, :])
                    linear = reduce(+, map(*, DFiP.(X[i, :]), ws))
                    observe(prob_equals(linear + error, DFiP(y[i])))         
                end
            ws[1]
    end

    inside_expectation = try expectation(code)
                         catch 
                            1.0
                         end

    prob_evidence = pr(allobservations(code))[true]
    return inside_expectation, prob_evidence
end

function linear_regression_collapsed_sample(total_bits, bits_sampled, n, p, X, y, NSAMPLES)
    samples = rand(Bernoulli(0.5), NSAMPLES, n+p, bits_sampled)
    samples = map(x -> if x == 1 true else false end, samples)
    
    mean = [linear_regression_sample(total_bits, n, p, X, y, samples[i, :, :]) for i in 1:NSAMPLES]
    num = sum(map(x -> x[1]*x[2], mean))
    den = sum(map(x -> x[2], mean))
    count = sum(map(x -> x[2] == 0.0, mean))
    @show num, den
    sampled_expectation = num/den
    return sampled_expectation, count
end