using Pkg; Pkg.activate(@__DIR__)
using Alea, Distributions

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

precision = 2
DFiP = DistFix{9+precision, precision}
num_pieces = 8
truncation = (-8.0, 8.0)
mult_arg = false

ys = DFiP.([3.33008960302557, 5.19543854472405, 5.88929762709886, 5.52449264517973, 5.31172037906861,
        7.1453284527505, 7.11693949967702, 10.2790569556659, 8.70290237657601, 4.91879758555161,
        5.9793649285972, 5.71069265888431, 5.82376740342438, 6.63877402512103, 7.42179960481787,
        9.62291014033926, 2.3662166776056, 5.13435595049398, 8.88839345256223, 4.82787281003398,
        6.66222539318123, 5.52684066394334, 5.1114875649346, 5.63288986028277, 4.38694756020315,
        5.57649838108011, 7.7437901545178, 3.97144535706026, 6.90655408345038, 5.34519996931202,
        5.82326082407921, 4.15702108539003, 6.81140925182179, 7.24764851401942, 5.49343534916886,
        8.28785318207118, 6.7638307279417, 4.90294078296499, 5.66570297954388, 5.20315542517743]);

y_lags = DFiP.([4.3838241041638, 3.93442675489932, 7.57050890065729, 4.53683034032583, 5.28768584504724,
        7.84145292649045, 8.09962392030284, 9.55146255046129, 8.73574461648241, 4.44520985772833,
        4.86994492644444, 4.09735724627972, 4.01458069570362, 8.93653732435778, 6.37760733487085,
        9.47473778631538, 3.34918157150969, 5.00719783334061, 8.86413662843406, 4.86521017467603,
        6.06770903747529, 6.16693980395794, 7.25456838915125, 5.95538431135938, 5.22133663948625,
        5.36950460318476, 9.45933439927176, 4.04464610107243, 6.75704792523757, 4.24326258972287,
        6.9590606178157, 3.89350344482809, 5.34843717515469, 8.38955592149869, 5.99861560808495,
        8.28150384919718, 7.6049918634817, 5.4332405702211, 5.35873385947198, 5.18218877464533]);

code = @dice begin
  
  beta1 = bitblast(DFiP, Normal(1, 1), num_pieces, -7.0, 9.0)
  beta2 = bitblast(DFiP, Normal(1, 1), num_pieces, -7.0, 9.0)
  sigma = uniform(DFiP, 0.0, 15.99999)

  for (y, y_lag) in zip(ys, y_lags)
    mean = beta1 + beta2 * y_lag
    gaussian_observe(DFiP, num_pieces, truncation[1], truncation[2], mean, sigma, y, mult=mult_arg)
  end
  beta1
end

# HMC-estimated ground truth: 1.363409828
@time expectation(code)