data {
  int<lower=0>  N;
  real y[N];
}
parameters {
  real mu;
}

model {
  mu ~ normal(0, 1);
  for (n in 1:N)
    target += normal(y[n], 1); 
}
