using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

if length(ARGS) == 0
    bits = 20
    pieces = 1024
else
    bits = parse(Int64, ARGS[1])
    pieces = parse(Int64, ARGS[2])
end

DFiP = DistFix{bits + 5, bits}

t = @timed pr(@dice begin 
            d1 = bitblast_exponential(DFiP, 4*Beta(8, 2), pieces, 0.0, 4.0)
            d2 = bitblast_exponential(DFiP, 8*Beta(5, 5), pieces, 0.0, 8.0)
            gpa1 = if flip(0.95) d1 else 
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
        end)

p = t.value
io = open(string("./benchmarks/GPA/results.txt"), "a")
@show bits, pieces, p[1.0], t.time
writedlm(io, [bits pieces p[1.0] t.time], ",")  
close(io)