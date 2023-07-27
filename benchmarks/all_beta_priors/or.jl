using Dice, Distributions
using Revise
using Plots
using DelimitedFiles
using BenchmarkTools
using Plots

# bits = 0
# pieces = 128
# n_vars = 100

bits = parse(Int64, ARGS[1])
pieces = parse(Int64, ARGS[2])
n_vars = parse(Int64, ARGS[3])

DFiP = DistFixedPoint{9 + bits, bits}


z = Vector(undef, n_vars)
prior = Vector(undef, n_vars)
for i in 1:n_vars
    prior[i] = uniform(DFiP, 0.0, 1.0)
    z[i] = parametrised_flip(prior[i])
	# z[i] = flip(0.5)
end
y = reduce(|, z)

d1 = ifelse(y, 
            continuous(DFiP, Normal(135, 8), pieces, 135-64.0, 135+64.0, true),
            continuous(DFiP, Normal(80, 8), pieces, 80-64.0, 80+64.0, true))
d2 = ifelse(y, 
            continuous(DFiP, Normal(135, 8), pieces, 135-64.0, 135+64.0, true),
            continuous(DFiP, Normal(80, 8), pieces, 80-64.0, 80+64.0, true))

t = @timed expectation(@dice begin
    observe(prob_equals(d1, DFiP(79.0)))
    observe(prob_equals(d2, DFiP(136.0)))
    prior[1]
end)
    
p = t.value
io = open(string("./benchmarks/or/results_")*string(n_vars)*string(".txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)
