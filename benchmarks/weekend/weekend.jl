using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

if length(ARGS) == 0
  bits = 20
  pieces = 4096
else
  bits = parse(Int64, ARGS[1])
  pieces = parse(Int64, ARGS[2])
end

DFiP = DistFix{4+bits, bits}

t = @timed pr(@dice begin

  isWeekend = flip(2/7)
  hour = if isWeekend
            bitblast_exponential(DFiP, Normal(5, 4), pieces, 0.0, 8.0)
        else
            bitblast_exponential(DFiP, Normal(2, 4), pieces, 0.0, 8.0)
        end
  observe(hour == DFiP(6.0))
  isWeekend
end)

p = t.value

io = open(string("./benchmarks/weekend/results.txt"), "a")
@show bits, pieces, p[1.0], t.time
writedlm(io, [bits pieces p[1.0] t.time], ",")  
close(io)