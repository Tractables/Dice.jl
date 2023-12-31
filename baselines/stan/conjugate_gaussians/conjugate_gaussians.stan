data {
  int<lower=1> T;
  array[T] real<lower=0> D;
}
parameters {
  real mu;
}
model {
  mu ~ normal(0, 1);
  D ~ normal(mu, 1);
}

