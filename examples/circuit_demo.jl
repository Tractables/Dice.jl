using Dice

# bit-width of our integers 
w = 10
# constant K
K = 500

code = @dice begin
	k = DistUInt{w}(K)

	x1 = uniform(DistUInt{w}, 8) 
	x2 = uniform(DistUInt{w}, 9)
	x3 = uniform(DistUInt{w}, 10)
	x4 = uniform(DistUInt{w}, 4)
	x5 = uniform(DistUInt{w}, 8)

	computed = ((x1 + x2) * x2) - ((x3 + x4) * (x4 + x5))

	check = computed > k
	return check 
end

@show pr(code, ignore_errors=true)
