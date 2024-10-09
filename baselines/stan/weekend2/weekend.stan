data {
  real hour;
}
transformed data {
  real m1;
  m1 = 0;
  real acc0 = 0;
  real acc1 = 0;

  acc0[isweekend_val] += bernoulli_lpmf(isweekend_val | (2 / 7));
  acc0[isweekend_val] += normal_lpdf(hour | (isweekend_val * 5 + (1 - isweekend_val) * 2),4);

  m1 += log_sum_exp(acc0);
}
model {
  target += m1;

}
generated quantities {
  int isweekend;
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(isweekend_val in 1 : 2){
      acc0[isweekend_val] += bernoulli_lpmf(isweekend_val | (2 / 7));
      acc0[isweekend_val] += normal_lpdf(hour | (isweekend_val * 5 + (1 - isweekend_val) * 2),4);

    }
    isweekend = categorical_logit_rng(acc0);
  }

}

