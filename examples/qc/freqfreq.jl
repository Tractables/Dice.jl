using Dice
abstract type GenerationParams{T} end
include("../../qc/benchmarks/benchmarks.jl")
I = DistUInt32
SEED = 0
out_dir="/tmp"
rs = RunState(Valuation(), Dict{String,ADNode}(), stdout, out_dir, MersenneTwister(SEED), nothing,nothing)

θ = [register_weight!(rs, string(i)) for i in 1:8]
G = frequency([
    θ[1] => frequency([θ[2] => I(1), θ[3] => I(2), θ[4] => I(3)]),
    θ[5] => frequency([θ[6] => I(3), θ[7] => I(4), θ[8] => I(5)]),
])
desired_dist = [
    I(1) => 0.2,
    I(2) => 0.2,
    I(3) => 0.2,
    I(4) => 0.2,
    I(5) => 0.2,
]
loss = kl_divergence(desired_dist, G)
train!(rs.var_vals, loss, epochs=2000, learning_rate=0.1)
print_adnodes_of_interest(rs, "")

# ADNodes of interest ():
# Dict("3" => 0.5834792022353119, "4" => 0.29176006955685957, "1" => 0.5, "5" => 0.5000000000000001, "2" => 0.5834792022353119, "6" => 0.2917600695568597, "7" => 0.5834792022353119, "8" => 0.5834792022353119)