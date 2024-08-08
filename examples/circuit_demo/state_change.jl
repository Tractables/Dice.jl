using Dice
using DelimitedFiles
using Plots

#=
    Uses the example functions from half_adder.jl to compute the probability of 
    carries changing when adding different distributions. 
=#

# The same functions from half_adder.jl
function half_adder(a, b)
    summ = xor(a, b)
    carry = a & b
    return summ, carry
end

function full_adder(a, b, c)
    s1, c1 = half_adder(a, b)
    s2, c2 = half_adder(s1, c)
    c3 = c1 | c2
    return s2, c3
end

# The add function from half_adder.jl, modified to return 
# an additional vector containing the internal carry values 
function add(a::DistUInt{W}, b::DistUInt{W}) where W
    summ = Vector(undef, W)
    carry = Vector(undef, W)
	carry_temp = false
    for i in W:-1:1
        # print(i)
        summ[i], carry_temp = full_adder(a.bits[i], b.bits[i], carry_temp)
		carry[i] = carry_temp
    end
    return DistUInt{W}(summ), carry
end

# Creates two distributions over 0, .., 7 (000, .., 111), then adds
a = uniform(DistUInt{3})
b = uniform(DistUInt{3})
s1, c1 = add(a, b)

# Creates two distributions over 0, .., 3 (000, .., 011), then adds
a = uniform(DistUInt{3}, 2)
b = uniform(DistUInt{3}, 2)
s2, c2 = add(a, b)

# Iterate over internal carry results to count the number of differences 
# between the two sums; this is a probabilistic value
carry_changes = DistUInt{3}(0)
for i in 1:3
	global carry_changes += ifelse(!prob_equals(c1[i], c2[i]), DistUInt{3}(1), DistUInt{3}(0))
end
result = pr(carry_changes)
bar(result, xlabel="Number of carry changes", ylabel="pr", legend=false)
savefig("./examples/circuit_demo/state_change.png")

println("Probability of state change")
println(result)
println("Plot saved in ./examples/circuit_demo/state_change.png")