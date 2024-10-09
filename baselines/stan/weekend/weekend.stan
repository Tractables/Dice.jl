data {
  int<lower=1> T;
  array[T] real<lower=0> D;
}
parameters {
}
transformed parameters {
  vector[2] fp;
  fp[1] = log(2.0/7);
  fp[2] = log(5.0/7);
  for (t in 1:T) {
	fp[1] = fp[1] + normal_lpdf(D[t] | 5, 4) - log(0.89435);
        fp[2] = fp[2] + normal_lpdf(D[t] | 2, 4) - log(0.69146);	
  }
}
model {
  target += log_sum_exp(fp);
}

