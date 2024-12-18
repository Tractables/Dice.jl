using Dice
using Distributions
include("data_generation.jl")

DFiP = DistFix{7, 2}
p = 5 # Number of features
n = 2 # Number of observations

w1 = bitblast(DFiP, Normal(0, 1), 8, -8.0, 8.0)
w2 = bitblast(DFiP, Normal(0, 1), 8, -8.0, 8.0)
x1 = DFiP(0.75)
x2 = DFiP(1.0)
y = DFiP(1.0)
noise = bitblast(DFiP, Normal(0, 1), 8, -8.0, 8.0)

w1 = DFiP([false, false, flip(0.5), true, false, true, false])

X, y, betas = generate_spike_slab(2, p, 2)


fs = [flip(0.5) for _ in 1:p]
slabs = [bitblast(DFiP, Normal(0, 2), 8, -8.0, 8.0) for _ in 1:p]
errors = [bitblast(DFiP, Normal(0, 1), 4, -8.0, 8.0) for _ in 1:n]

priors = [ifelse(fs[i], DFiP(0.0), slabs[i]) for i in 1:p]




code = @dice begin
        for i in 1:n
                linear = reduce(+, map(*, DFiP.(X[i, :]), priors))
                observe(prob_equals(linear + errors[i], DFiP(y[i])))  
        end
        fs[5]
end

dump_dot(returnvalue(code) & allobservations(code), filename="spike_slab.dot")