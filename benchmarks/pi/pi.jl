using Dice, Distributions
using DelimitedFiles

b = ARGS[1]

p = pr(@dice begin
            x = uniform(DistFixedPoint{b+2, b}, 1/2^b, 1.0 + 1/2^b)
            y = uniform(DistFixedPoint{b+2, b}, 1/2^b, 1.0 + 1/2^b)
            t = round(x/y)
            !t.number.number.bits[2]     
end; ignore_errors=true)


io = open(string("./benchmarks/pi/results.txt"), "a")
@show b, p[1.0]
writedlm(io, [b p[1.0]], ",")  
close(io)