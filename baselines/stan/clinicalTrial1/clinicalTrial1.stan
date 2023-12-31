data {
  int N;
  int controlGroupFlip[N];
  int treatedGroupFlip[N];
}
parameters {
  real<lower=0, upper=1> probAll;
  real<lower=0, upper=1> probControl;
  real<lower=0, upper=1> probTreated;

}
transformed parameters {
  real m1;
  m1 = 0;
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(isEffective_val in 1 : 2){
      acc0[isEffective_val] += bernoulli_lpmf(isEffective_val-1 | 0.5);
      if((isEffective_val > 1)){
        for(n in 1 : N){
          acc0[isEffective_val] += bernoulli_lpmf(controlGroupFlip[n] | probControl);
          acc0[isEffective_val] += bernoulli_lpmf(treatedGroupFlip[n] | probTreated);

        }

      }
      else{
        for(n in 1 : N){
          acc0[isEffective_val] += bernoulli_lpmf(controlGroupFlip[n] | probAll);
          acc0[isEffective_val] += bernoulli_lpmf(treatedGroupFlip[n] | probAll);

        }

      }
    }
    m1 += log_sum_exp(acc0);
  }

}
model {
  probControl ~ uniform(0, 1);
  probTreated ~ uniform(0, 1);
  probAll ~ uniform(0, 1);
  target += m1;

}
generated quantities {
  int isEffective;
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(isEffective_val in 1 : 2){
      acc0[isEffective_val] += bernoulli_lpmf(isEffective_val-1 | 0.5);
      if((isEffective_val > 1)){
        for(n in 1 : N){
          acc0[isEffective_val] += bernoulli_lpmf(controlGroupFlip[n] | probControl);
          acc0[isEffective_val] += bernoulli_lpmf(treatedGroupFlip[n] | probTreated);

        }

      }
      else{
        for(n in 1 : N){
          acc0[isEffective_val] += bernoulli_lpmf(controlGroupFlip[n] | probAll);
          acc0[isEffective_val] += bernoulli_lpmf(treatedGroupFlip[n] | probAll);

        }

      }
    }
    isEffective = categorical_logit_rng(acc0);
  }

}
