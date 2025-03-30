data {
  int<lower=0>  N;
  real y[N];
}
parameters {
  vector[2] mu;
}
model {
  mu[1] ~ uniform(-16, 16);
  mu[2] ~ uniform(-16, 16);
  for (n in 1:N)
    target += log_mix(2/3,
                     normal_lpdf(y[n] | mu[1], 1),
                     normal_lpdf(y[n] | mu[2], 1));
}
