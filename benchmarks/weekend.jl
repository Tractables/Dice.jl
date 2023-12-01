using Pkg; Pkg.activate(@__DIR__)
using Dice, Distributions

precision = 5
DFiP = DistFix{9+precision, precision}
num_pieces = 128

code = @dice begin

  isWeekend = flip(2/7)
  hour = if isWeekend
            bitblast(DFiP, Normal(5, 4), num_pieces, 0.0, 8.0)
        else
            bitblast(DFiP, Normal(2, 4), num_pieces, 0.0, 8.0)
        end
  observe(hour == DFiP(6.0))
  isWeekend
end

# HMC-estimated ground truth: 1.363409828
@time pr(code)