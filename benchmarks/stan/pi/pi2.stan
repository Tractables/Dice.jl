data {
}
parameters {
  real<lower=0, upper=1> u1;
  real<lower=0, upper=1> u2;
}
transformed parameters {
    real lp[2];
    lp[fmod(round(u1/u2), 2.0)] = uniform_lpdf(u1) + uniform_lpdf(u2);    
}
model {
  u1 ~ uniform(0, 1);
  u2 ~ uniform(0, 1);
}

