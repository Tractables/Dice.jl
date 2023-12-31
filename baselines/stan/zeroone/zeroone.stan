data {
  int<lower=0> N;
  int y[N];
  real x1[N];
}
parameters {
  real<lower=-10, upper=10> w1;
  real<lower=-10, upper=10> w2;
}
transformed parameters {
  real lp;
  lp = 0;
  for (i in 1:N) {
      lp += (y[i]*(x1[i]*w1 + w2)) < 0 ? 0 : 1;
  }
}
model {
  w1 ~ uniform(-8,8);
  w2 ~ uniform(-8,8);
  target += lp;
}
