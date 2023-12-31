data {
  int<lower=0> J;
  int<lower=0> N;
  int<lower=1,upper=J> county[N];
  vector[N] y;
}
parameters {
  real<lower=-4,upper=4> a;
  real<lower=0,upper=8> sigma_y;
}

model {
  a ~ uniform(-4, 4);
  sigma_y ~ uniform(0, 8);
  y ~ normal(a, sigma_y);
}
