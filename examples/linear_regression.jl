using Dice
using Revise
using Distributions
using Plots
using DelimitedFiles


bits = 5
DFiP = DistFix{9+bits, bits}

if length(ARGS) != 0
    nobs = parse(Int64, ARGS[1])
    nweights = parse(Int64, ARGS[2])
else
    nobs = 10
    nweights = 3
end

true_weights = collect(0:nweights-1)
xs = [rand(Uniform(-2, 2), nweights) for i in 1:nobs]
ys = [mapreduce(x->x[1]*x[2], +, zip(xs[i], true_weights)) for i in 1:nobs]
error = rand(Normal(0, 1), nobs)
ys = ys+error

weight_priors = [bitblast(DFiP, Normal(0, 2), 64, -8.0, 8.0) for i in 1:nweights]

error_dist = bitblast(DFiP, Normal(0, 2), 64, -8.0, 8.0)


code = @dice begin
            for i in 1:nobs
                error_dist = bitblast(DFiP, Normal(0, 1), 64, -8.0, 8.0)
                observe(prob_equals(DFiP(ys[i]), mapreduce(x -> DFiP(x[1])*x[2], +, zip(xs[i], weight_priors)) + error_dist))           
            end
        weight_priors[2]
end
p = @timed expectation(code, ignore_errors=true)

io = open(string("./linear_regression.txt"), "a")
@show p
writedlm(io, [nweights nobs p.time], ",")  
close(io)