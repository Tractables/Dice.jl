using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

precision = parse(Int64, ARGS[1])
num_pieces = parse(Int64, ARGS[2])

p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFixedPoint{4+precision, precision}

t = @timed pr(@dice begin

  isWeekend = flip(2/7)
  hour = if isWeekend
            continuous(DFiP, Normal(5, 4), num_pieces, 0.0, 8.0)
        else
            continuous(DFiP, Normal(2, 4), num_pieces, 0.0, 8.0)
        end
  observe(hour == DFiP(6.0))
  isWeekend
end)

p = t.value

io = open(string("./benchmarks/weekend/results.txt"), "a")
@show precision, num_pieces, p[1.0], t.time
writedlm(io, [precision num_pieces p[1.0] t.time], ",")  
close(io)