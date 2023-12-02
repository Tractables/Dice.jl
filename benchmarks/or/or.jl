using Dice, Distributions
using Revise
using Plots
using DelimitedFiles
using BenchmarkTools
using Plots

# bits = 9
# pieces = 1024
# n_vars = 10

bits = parse(Int64, ARGS[1])
pieces = parse(Int64, ARGS[2])
n_vars = parse(Int64, ARGS[3])

DFiP = DistFix{7 + bits, bits}

prior = uniform(DFiP, 0.0, 1.0)
z = Vector(undef, n_vars)
z[1] = parametrised_flip(prior)
for i in 2:n_vars
	z[i] = flip(0.5)
end
y = reduce(|, z)

d1 = ifelse(y, 
            bitblast_exponential(DFiP, Normal(-1, 1), pieces, -9.0, 7.0),
            bitblast_exponential(DFiP, Normal(1, 1), pieces, -7.0, 9.0))
d2 = ifelse(y, 
            bitblast_exponential(DFiP, Normal(-1, 1), pieces, -9.0, 7.0),
            bitblast_exponential(DFiP, Normal(1, 1), pieces, -7.0, 9.0))

t = @timed expectation(@dice begin
    observe(prob_equals(d1, DFiP(-1.5)))
    observe(prob_equals(d2, DFiP(1.5)))
    prior
end)
    
p = t.value
io = open(string("./benchmarks/or/results_")*string(n_vars)*string(".txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)
