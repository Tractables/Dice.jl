using Dice, Distributions
using Revise
using Plots
using DelimitedFiles
using BenchmarkTools
using Plots

n_vars = if length(ARGS) > 0 ARGS[1] else 5 end

if length(ARGS) > 1
    bits = parse(Int64, ARGS[2])
    pieces = parse(Int64, ARGS[3])
else
    bits = 20
    pieces = 32
end

DFiP = DistFix{9 + bits, bits}


z = Vector(undef, n_vars)
prior = Vector(undef, n_vars)
for i in 1:n_vars
    prior[i] = uniform(DFiP, 0.0, 1.0)
    z[i] = parametrised_flip(prior[i])
	# z[i] = flip(0.5)
end
y = reduce(|, z)

d1 = ifelse(y, 
            bitblast_exponential(DFiP, Normal(135, 8), pieces, 135-64.0, 135+64.0),
            bitblast_exponential(DFiP, Normal(80, 8), pieces, 80-64.0, 80+64.0))
d2 = ifelse(y, 
            bitblast_exponential(DFiP, Normal(135, 8), pieces, 135-64.0, 135+64.0),
            bitblast_exponential(DFiP, Normal(80, 8), pieces, 80-64.0, 80+64.0))

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
