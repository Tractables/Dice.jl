data {
}
parameters {
  real<lower=0, upper=64> e;
  real<lower=0, upper=64> fs;
  real<lower=0, upper=64> ss;
}
transformed parameters {
  real<lower=0> cfs;
  real<lower=0> cr;
  cfs = e + fs;
  cr = cfs + ss;
}
model {
  e ~ normal(5, 1);
  fs ~ normal(10, 3);
  ss ~ normal(15, 3);
}

