using Distributions
using LogExpFunctions
include("ground_truth.jl")
include("data_generation.jl")
include("collapsed_sampling.jl")

n = 2 # Number of observations
p = 5 # Number of features
X, y, beta = generate_linear(n, p)
mu, sigma = ground_truth_linear(X, y, [2 for _ in 1:p], 1)

total_bits = 5
bits_sampled = 7
NSAMPLES = 100

samples = rand(Bernoulli(0.5), NSAMPLES, n+p, bits_sampled)
samples = map(x -> if x == 1 true else false end, samples)

# mean = [linear_regression_sample(total_bits, n, p, X, y, samples[i, :, :]) for i in 1:NSAMPLES]

bits = total_bits
s = samples[1, :, :]

DFiP = DistFix{9 + bits, bits}
pieces = 2^(bits+5 - size(s)[2])
@assert size(s)[1] == n+p

# @show DFiP, size(s)[2]
ws = [gaussian_bitblast_sample(DFiP, 0.0, sqrt(2.0), pieces, -16.0, 16.0, s[i, :]) for i in 1:p]
code = @dice begin
            for i in 1:n
                error = bitblast_linear(DFiP, Normal(0.0, 1.0), 2^(4 + bits), -8.0, 8.0)
                # error = gaussian_bitblast_sample(DFiP, 0.0, 1.0, Int(pieces/2), -8.0, 8.0, s[i+p, :])
                linear = reduce(+, map(*, DFiP.(X[i, :]), ws))
                observe(prob_equals(linear + error, DFiP(y[i])))         
            end
        ws[1]
end

@show num_nodes(returnvalue(code))
@show num_nodes(allobservations(code))

pr(code)

code2 = @dice begin
    for i in 1:n
        error = bitblast_linear(DFiP, Normal(0.0, 1.0), 2^(4 + bits), -8.0, 8.0)
        # error = gaussian_bitblast_sample(DFiP, 0.0, 1.0, Int(pieces/2), -8.0, 8.0, s[i+p, :])
        linear = reduce(+, map(*, DFiP.(X[i, :]), ws))
        observe(prob_equals(DFiP(y[i]) - linear, error))         
    end
    ws[1]
end

@show num_nodes(returnvalue(code2))
@show num_nodes(allobservations(code2))

pr(code2)


function squarex(x::DistFix{W, F}) where {W, F}
    square_coeff = Matrix(undef, W, W)
    for i in 1:W
        for j in 1:W
            if i == j
                square_coeff[i, j] = x.mantissa.number.bits[i]
            elseif j < i
                square_coeff[i, j] = x.mantissa.number.bits[i] & x.mantissa.number.bits[j]
            else
                square_coeff[i, j] = false
            end
        end
    end
    square_coeff
end

function fixed_abs(x::DistFix{W, F}) where {W, F}
    unsigned_abs(x.mantissa)
end


code3 = @dice begin
    a = Vector(undef, n)
    for i in 1:n
        linear = DFiP(y[i]) - reduce(+, map(*, DFiP.(X[i, :]), ws))
        absolute = DistFix{9 + bits, bits}(fixed_abs(linear).bits)
        squared_x = squarex(absolute)
        a[i] = squared_x[5, 5]
        for i in 1:9+bits
            for j in 1:i
                i_hat = 2.0^(9-i)
                j_hat = 2.0^(9-j)
                
                flip_param = exp(-i_hat * j_hat/(2^(i == j)))
                @show flip_param
                # if squared_x[i, j] observe(flip(flip_param)) else true end
                # squared_x[i, j] && observe(flip(flip_param))
                observe(!squared_x[i, j] | (squared_x[i, j] & flip(flip_param)))
            end
        end
    end
    ws[1]
    # a[2]
end

@show num_nodes(returnvalue(code3))
@show num_nodes(allobservations(code3))

pr(code3)

code4 = @dice begin
    for i in 1:n
        linear = DFiP(y[i]) - reduce(+, map(*, DFiP.(X[i, :]), ws))
        squared_x = (linear * linear).mantissa.number.bits
        for i in 1:length(squared_x)
            flip_param = exp(-2.0^(9-i-1))
            # flip_param = flip_param/(1+flip_param)
            observe(!squared_x[i] | (squared_x[i] & flip(flip_param)))
            # if squared_x.mantissa.number.bits[i] observe(flip(flip_param)) else true end
            # observe(prob_equals(squared_x.mantissa.number.bits[i], flip(flip_param)))
        end
    end
    ws[1]
end

@show num_nodes(returnvalue(code4))
@show num_nodes(allobservations(code4))

pr(code4)






inside_expectation = try expectation(code)
                        catch 
                        1.0
                        end

prob_evidence = pr(allobservations(code))[true]
return inside_expectation, prob_evidence

num = sum(map(x -> x[1]*x[2], mean))
den = sum(map(x -> x[2], mean))
count = sum(map(x -> x[2] == 0.0, mean))
@show num, den
sampled_expectation = num/den
return sampled_expectation, count