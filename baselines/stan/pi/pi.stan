data {
}
parameters {
  real<lower=0, upper=1> u1;
  real<lower=0, upper=1> u2;
}
transformed parameters {
    real<lower=0, upper=1> answer;
    answer = fmod(round(u1/u2), 2.0);
}
model {
  u1 ~ uniform(0, 1);
  u2 ~ uniform(0, 1);
}

