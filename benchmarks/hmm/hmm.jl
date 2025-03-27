using Alea, Distributions
using Revise
using Plots
using DelimitedFiles
using BenchmarkTools
using Plots

# bits = 5
# pieces = 128
# n_vars = 10

bits = parse(Int64, ARGS[1])
pieces = parse(Int64, ARGS[2])
n_vars = parse(Int64, ARGS[3])

DFiP = DistFix{5 + bits, bits}
theta1 = uniform(DFiP, 0.0, 1.0)

z = Vector(undef, n_vars)
y = Vector(undef, n_vars)
z[1] = parametrised_flip(theta1)
y[1] = ifelse(z[1], 
            bitblast_exponential(DFiP, Normal(-1, 1), pieces, -9.0, 7.0),
            bitblast_exponential(DFiP, Normal(1, 1), pieces, -7.0, 9.0))

for i in 2:(n_vars-1)
    z[i] = ifelse(z[i-1], flip(0.5), flip(0.5))
    y[i] = ifelse(z[i], 
                bitblast_exponential(DFiP, Normal(-1, 1), pieces, -9.0, 7.0),
                bitblast_exponential(DFiP, Normal(1, 1), pieces, -7.0, 9.0))
end

z[n_vars] = ifelse(z[n_vars-1], flip(0.5), flip(0.5))
d1 = ifelse(z[n_vars], 
            bitblast_exponential(DFiP, Normal(-1, 1), pieces, -9.0, 7.0),
            bitblast_exponential(DFiP, Normal(1, 1), pieces, -7.0, 9.0))
d2 = ifelse(z[n_vars], 
            bitblast_exponential(DFiP, Normal(-1, 1), pieces, -9.0, 7.0),
            bitblast_exponential(DFiP, Normal(1, 1), pieces, -7.0, 9.0))

t = @timed expectation(@dice begin
            observe(prob_equals(d1, DFiP(-1.5)))
            observe(prob_equals(d2, DFiP(1.5)))
            theta1
end)

p = t.value
io = open(string("./benchmarks/hmm/results_")*string(n_vars)*string(".txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)