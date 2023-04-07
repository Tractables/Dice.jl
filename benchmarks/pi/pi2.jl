using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

p = pr(@dice uniform(DistUInt{3}); ignore_errors=true)

# b = parse(Int64, ARGS[1])

# for a = 1:20
    a = 3
    b = a
    t = @timed pr(@dice begin
                x = uniform(DistFixedPoint{b+2, b}, 1/2^b, 1.0 + 1/2^b)
                y = uniform(DistFixedPoint{b+2, b}, 1/2^b, 1.0 + 1/2^b)
                x = DistFixedPoint{b+2, 1}(x.number)
                y = DistFixedPoint{b+2, 1}(y.number)
                t = round(x/y)
                # !t.number.number.bits[2]
                !t.number.number.bits[b+1]        
    end;ignore_errors=true)
    p = t.value


    io = open(string("./benchmarks/pi/results2.txt"), "a")
    @show b, p[1.0], t.time
    writedlm(io, [b p[1.0] t.time], ",")  
    close(io)
# end