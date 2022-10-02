using Pkg; Pkg.activate("$(@__DIR__)/../")
using Dice, Distributions

#=
data {
  int<lower=0> N;
  vector[N] y;
  vector[N] y_lag;
}
parameters {
  vector[2] beta;
  real<lower=0> sigma;
}
model {
  beta ~ normal(1,1);
  y ~ normal(beta[1] + beta[2] * y_lag, sigma);
}
=#

precision = 1
num_pieces = 16

DFiP = DistFixedPoint{20+precision, precision}

ys = DFiP.([12.1374259163952, 26.6903103048018, 38.5878897957254, 30.4930667829189, 39.2801876119107,
            20.4174324499166, 25.7777563431966, 11.5919826316299, 37.3521894576722, 42.3729512347165,
            33.1974931235148, 18.3925621724044, 38.2093756620254, 26.5178923853568, 4.52268843482463,
            17.4645068462391, 20.0241067156045, 14.6755540100198, 12.9841025634912, 42.3191772083172,
            29.558684814201, 30.911111042245, 25.211786124301, 22.3592414735694, 30.7775798797013,
            16.8625137818992, 28.5736618568681, 19.5770593955495, 48.3010147870319, 31.2281915401234,
            21.601456892799, 29.6730840465467, 30.9093803330748, 17.5249474584363, 37.2377810832606,
            14.6787881367532, 24.770796317115, 34.6698348225234, 30.3842636610215, 24.5081046666978]);

code = @dice begin
  
  beta = uniform(DFiP, -32.0, 32.0)
  sigma = uniform(DFiP, 0.0, 64.0)

  for y in ys
    unitgaussian = continuous(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
    gaussian = sigma * unitgaussian + beta
    observe(gaussian == y)
  end
  beta
end

# HMC-estimated ground truth: ?
@time expectation(code)