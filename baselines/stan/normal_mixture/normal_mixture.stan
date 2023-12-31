data {
  int<lower=0>  N;
  real y[N];
}
parameters {
  real<lower=0,upper=1> theta;
  vector[2] mu;
}

model {
  mu[1] ~ normal(-10,1);
  mu[2] ~ normal(10,1);
  for (n in 1:N)
    target += log_mix(theta,
                     normal_lpdf(y[n] | mu[1], 1),
                     normal_lpdf(y[n] | mu[2], 1));
}
