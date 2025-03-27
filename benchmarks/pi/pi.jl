using Revise
using Alea, Distributions
using DelimitedFiles
using BenchmarkTools

if length(ARGS) == 0
    b = 8
else
    b = parse(Int64, ARGS[1])
end

t = @timed pr(@dice begin
            x = uniform(DistFix{b+2, b}, 1/2^b, 1.0 + 1/2^b)
            y = uniform(DistFix{b+2, b}, 1/2^b, 1.0 + 1/2^b)
            x = DistFix{b+2, 1}(x.number)
            y = DistFix{b+2, 1}(y.number)
            t = round(x/y)
            # !t.number.number.bits[2]
            !t.number.number.bits[b+1]        
end;ignore_errors=true)
p = t.value


io = open(string("./benchmarks/pi/results2.txt"), "a")
@show b, p[1.0], t.time
writedlm(io, [b p[1.0] t.time], ",")  
close(io)