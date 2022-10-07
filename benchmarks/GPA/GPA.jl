using Dice, Distributions
using DelimitedFiles

bits = ARGS[1]
pieces = ARGS[2]

DFiP = DistFixedPoint{bits + 5, bits}
d1 = continuous(DFiP, 4*Beta(8, 2), pieces, 0.0, 4.0)
d2 = continuous(DFiP, 8*Beta(5, 5), pieces, 0.0, 8.0)
        
pr(@dice begin gpa1 = if flip(0.95) d1 else 
            if flip(0.15) DFiP(4.0) else
                DFiP(0.0)
            end
        end

gpa2 = if flip(0.99) d2 else 
            if flip(0.1) DFiP(8.0) else
                DFiP(0.0)
            end
        end

n = flip(0.25)
final = if n gpa1 else gpa2 end
observe(prob_equals(final, DFiP(0.0)))
n
end; ignore_errors=true)

io = open(string("./benchmarks/GPA/results.txt"), "a")
@show b, p[1.0]
writedlm(io, [b p[1.0]], ",")  
close(io)