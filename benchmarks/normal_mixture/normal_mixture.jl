using Revise
using Alea, Distributions
using DelimitedFiles
using BenchmarkTools

if length(ARGS) == 0
  precision = 20
  num_pieces = 512
  flag = 1
else
  precision = parse(Int64, ARGS[1])
  num_pieces = parse(Int64, ARGS[2])
  flag = parse(Int64, ARGS[3])
end

DFiP = DistFix{6+precision, precision}
truncation = (-8.0, 8.0)
mult_arg = true

ys = DFiP.([10.0787617156523, -9.51866467444093, 9.73922587306449, 11.5662681883816, 9.62798489000074, -9.60265090119919, 8.90114345923455, 10.866328444034, 10.5347883361026, 8.60577222463504, -10.625227428575, -9.08615131315038, -8.99280046532217, 9.43533905966944, 8.92696803962787, 9.642301288006, 9.42066621557773, 9.90838406119759, 9.63911912487384, 7.55585122379505, 9.58069898235901, 9.63228461457187, -9.99589804304319, 8.61024296515084, -10.4988882191036, -8.45028703711596, 9.76066425342707, -8.68129886943495, 9.83763492226261, 7.29698608457303, 8.78881675784227, 10.6057117460834, 10.2807363791435, 9.54352982843898, -10.9911972452721, 12.2061931600758, 7.76887153466896, 10.7523541087606, -9.98525551020183, 10.6248182699128]);

t = @timed expectation(@dice begin
  
  theta = uniform(DFiP, 0.0, 1.0)
  mu1 = bitblast_exponential(DFiP, Normal(-10, 1), num_pieces, -18.0, -2.0)
  mu2 = bitblast_exponential(DFiP, Normal(10, 1), num_pieces, 2.0, 18.0)

  for y in ys
    c1 = bitblast_exponential(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
    c2 = bitblast_exponential(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
    a = ifelse(parametrised_flip(theta), mu1 + c1, mu2 + c2)
    observe(a == y)
  end
  
  if flag == 1
      theta
  elseif flag == 2
      mu1
  else 
      mu2
  end
end)

p = t.value

io = open(string("./benchmarks/normal_mixture/results.txt"), "a")
@show precision, num_pieces, p, flag, t.time
writedlm(io, [precision num_pieces p flag t.time], ",")  
close(io)