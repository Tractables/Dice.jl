data {
  real d1;
  real d2;

}
parameters {
    real<lower=0, upper=1> prior;

}
transformed parameters {
	real m1[8];
  m1 = rep_array(0, 8);
  for(z4 in 1 : 2){
    for(z3 in 1 : 2){
      for(z2 in 1 : 2){
        { vector[2] acc0;
          acc0 = rep_vector(0,2);
          for(z1_val in 1 : 2){
            acc0[z1_val] += bernoulli_lpmf(z1_val  - 1 | prior);
            acc0[z1_val] += bernoulli_lpmf(z2  - 1 | 0.5);
            acc0[z1_val] += bernoulli_lpmf(z3  - 1 | 0.5);
            acc0[z1_val] += bernoulli_lpmf(z4  - 1 | 0.5);
            if((((((z1_val + z2) + z3) + z4) - 4) > 0)){
              acc0[z1_val] += normal_lpdf(d1 | 1,1);
              acc0[z1_val] += normal_lpdf(d2 | 1,1);

            }
            else{
              acc0[z1_val] += normal_lpdf(d1 | -1,1);
              acc0[z1_val] += normal_lpdf(d2 | -1,1);

            }
          }
          m1[(z2 - 1)*4+(z3-1)*2+(z4-1)*1+1] += log_sum_exp(acc0);
        }

      }

    }

  }

	real m2[4];
	real m3[2];
  real m4;
  m2 = rep_array(0, 4);
  for(z4 in 1 : 2){
    for(z3 in 1 : 2){
      { vector[2] acc0;
        acc0 = rep_vector(0,2);
        for(z2_val in 1 : 2){
          acc0[z2_val] += m1[(z2_val - 1)*4+(z3-1)*2+(z4-1)*1+1];

        }
        m2[(z3 - 1)*2+(z4-1)*1+1] += log_sum_exp(acc0);
      }

    }

  }
  m3 = rep_array(0, 2);
  for(z4 in 1 : 2){
    { vector[2] acc0;
      acc0 = rep_vector(0,2);
      for(z3_val in 1 : 2){
        acc0[z3_val] += m2[(z3_val - 1)*2+(z4-1)*1+1];

      }
      m3[z4] += log_sum_exp(acc0);
    }

  }
  m4 = 0;
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z4_val in 1 : 2){
      acc0[z4_val] += m3[(z4_val - 1)*1+1];

    }
    m4 += log_sum_exp(acc0);
  }


}
model {
  prior ~ beta(1, 1);
  target += m4;

}
generated quantities {
  int z1;
  int z2;
  int z3;
  int z4;
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z4_val in 1 : 2){
      acc0[z4_val] += m3[(z4_val - 1)*1+1];

    }
    z4 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z3_val in 1 : 2){
      acc0[z3_val] += m2[(z3_val - 1)*2+(z4-1)*1+1];

    }
    z3 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z2_val in 1 : 2){
      acc0[z2_val] += m1[(z2_val - 1)*4+(z3-1)*2+(z4-1)*1+1];

    }
    z2 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z1_val in 1 : 2){
      acc0[z1_val] += bernoulli_lpmf(z1_val  - 1 | prior);
      acc0[z1_val] += bernoulli_lpmf(z2  - 1 | 0.5);
      acc0[z1_val] += bernoulli_lpmf(z3  - 1 | 0.5);
      acc0[z1_val] += bernoulli_lpmf(z4  - 1 | 0.5);
      if((((((z1_val + z2) + z3) + z4) - 4) > 0)){
        acc0[z1_val] += normal_lpdf(d1 | 1,1);
        acc0[z1_val] += normal_lpdf(d2 | 1,1);

      }
      else{
        acc0[z1_val] += normal_lpdf(d1 | -1,1);
        acc0[z1_val] += normal_lpdf(d2 | -1,1);

      }
    }
    z1 = categorical_logit_rng(acc0);
  }

}
