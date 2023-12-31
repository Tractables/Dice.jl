data {
  int<lower=0>  N;
  real y[N];
}
parameters {
  real<lower=-10, upper=-10> mu;
}

model {
  mu ~ normal(0, 1);
  for (n in 1:N)
    target += normal(y[n], 1); 
}
