using Dice
using DelimitedFiles
using BenchmarkTools
using Plots

# bit-width of our integers 
w = 10
# constant K
K = 256

function interleave_uniforms(widths::Vector{Int})
	sort_widths = sort(widths, rev=true)
	result = [Vector(undef, sort_widths[1]) for i in 1:length(widths)]
	for j in sort_widths[1]:-1:1
		for i in 1:length(widths)
			result[i][j] = j <= (sort_widths[1] - sort_widths[i]) ? false : flip(0.5)
		end
	end
	result = [DistUInt{sort_widths[1]}(i) for i in result]
	result
end

code = @dice begin
	k = DistUInt{w}(K)

	x3, x2, x1, x5, x4 = interleave_uniforms([8, 9, 10, 4, 8])
	sum1 = x1 + x2
    sum2 = x3 + x4
    sum3 = x4 + x5
    mult1 = sum1 * x2
    mult2 = sum2 * sum3
    (mult1 + mult2) > k
end
p = pr(code, ignore_errors=true) # Takes about 4 minutes