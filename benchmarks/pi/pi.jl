using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

if length(ARGS) == 0
    b = 9
else
    b = parse(Int64, ARGS[1])
end

function round(n::DistFix{W, F}) where {W, F}
    ifelse(n.mantissa.number.bits[W-F+1], 
        DistFix{W-F, 0}(n.mantissa.number.bits[1:W-F]) + DistFix{W-F, 0}(1.0)
    ,
    DistFix{W-F, 0}(n.mantissa.number.bits[1:W-F]))
end

t = @timed pr(@dice begin
            x = uniform(DistFix{b+2, b}, 1/2^b, 1.0 + 1/2^b)
            y = uniform(DistFix{b+2, b}, 1/2^b, 1.0 + 1/2^b)
            x = DistFix{b+2, 1}(x.mantissa)
            y = DistFix{b+2, 1}(y.mantissa)
            t = round(x/y)
            # !t.number.number.bits[2]
            !t.mantissa.number.bits[b+1]        
end;ignore_errors=true)
p = t.value


io = open(string("./benchmarks/pi/results.txt"), "w")
@show b, p[1.0], t.time
writedlm(io, [b p[1.0] t.time], ",")  
close(io)