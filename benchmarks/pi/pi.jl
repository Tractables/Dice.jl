using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

p = pr(@dice uniform(DistUInt{3}); ignore_errors=true)

b = parse(Int64, ARGS[1])

b = 6 
x_bits = Vector(undef, b+3)
y_bits = Vector(undef, b+3)
t = pr(@dice begin

            # for i = b:-1:1
            #     x_bits[i] = flip(0.5)
            #     y_bits[i] = flip(0.5)
            # end
            # for i = b+1:b+3
            #     x_bits[i] = false
            #     y_bits[i] = false
            # end

            # x = DistFixedPoint{b+3, b}(reverse(x_bits)) + DistFixedPoint{b+3, b}(1/2^b)
            # y = DistFixedPoint{b+3, b}(reverse(y_bits)) + DistFixedPoint{b+3, b}(1/2^b)
        
            x = uniform(DistFixedPoint{b+2, b}, 1/2^b, 1.0 + 1/2^b)
            y = uniform(DistFixedPoint{b+2, b}, 1/2^b, 1.0 + 1/2^b)
            x = DistFixedPoint{b+2, 1}(x.number)
            y = DistFixedPoint{b+2, 1}(y.number)
            t = round(x/y)
            # !t.number.number.bits[2]
            !t.number.number.bits[b+1]        
end; ignore_errors=true)
p = t.value


io = open(string("./benchmarks/pi/results.txt"), "a")
@show b, p[1.0], t.time
writedlm(io, [b p[1.0] t.time], ",")  
close(io)