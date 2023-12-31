data {
  int N;  
  int clicks0[N];
  int clicks1[N];
}
parameters {
  real<lower=0, upper=1> similarityAll;
  real<lower=0, upper=1> beta1[N];
  real<lower=0, upper=1> beta2[N];
}
model {
  similarityAll ~ uniform(0.0, 1.0);
  for (i in 1:N) {
    beta1[i] ~ uniform(0.0, 1.0);
    beta2[i] ~ uniform(0.0, 1.0);
    target += bernoulli_lpmf(clicks0[i] | beta1[i]);
    target += log_mix(similarityAll, bernoulli_lpmf(clicks1[i] | beta1[i]), bernoulli_lpmf(clicks1[i] | beta2[i])); 
  }
}
