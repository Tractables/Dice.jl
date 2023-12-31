data {
}
parameters {
  real mu1;
  real mu2;
}
transformed parameters {
  real ans;
  ans = mu1 + mu2;
}
model {
  mu1 ~ normal(0, 1);
  mu2 ~ normal(0, 1);
}

