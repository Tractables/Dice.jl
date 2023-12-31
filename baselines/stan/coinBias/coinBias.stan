data {
  int<lower=0> N;
  int y[N];
}
parameters {
  real<lower=0, upper=1> b;
}
model {
  b ~ beta(2, 5);
  for (i in 1:N) {
    target += bernoulli_lpmf(y[i] | b);
  }
}
