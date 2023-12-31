data {
  real d1;
  real d2;

}
parameters {
  real<lower=0, upper=1> prior1;
  real<lower=0, upper=1> prior2;
  real<lower=0, upper=1> prior3;
  real<lower=0, upper=1> prior4;
  real<lower=0, upper=1> prior5;

}
transformed parameters {
	real m1[16];
  m1 = rep_array(0, 16);
  for(z5 in 1 : 2){
    for(z4 in 1 : 2){
      for(z3 in 1 : 2){
        for(z2 in 1 : 2){
          { vector[2] acc0;
            acc0 = rep_vector(0,2);
            for(z1_val in 1 : 2){
              acc0[z1_val] += bernoulli_lpmf(z1_val  - 1 | prior1);
              acc0[z1_val] += bernoulli_lpmf(z2  - 1 | prior2);
              acc0[z1_val] += bernoulli_lpmf(z3  - 1 | prior3);
              acc0[z1_val] += bernoulli_lpmf(z4  - 1 | prior4);
              acc0[z1_val] += bernoulli_lpmf(z5  - 1 | prior5);
              if(((((((z1_val + z2) + z3) + z4) + z5) - 5) > 0)){
                acc0[z1_val] += normal_lpdf(d1 | 135,8);
                acc0[z1_val] += normal_lpdf(d2 | 135,8);

              }
              else{
                acc0[z1_val] += normal_lpdf(d1 | 80,8);
                acc0[z1_val] += normal_lpdf(d2 | 80,8);

              }
            }
            m1[(z2 - 1)*8+(z3-1)*4+(z4-1)*2+(z5-1)*1+1] += log_sum_exp(acc0);
          }

        }

      }

    }

  }

	real m2[8];
	real m3[4];
	real m4[2];
  real m5;
  m2 = rep_array(0, 8);
  for(z5 in 1 : 2){
    for(z4 in 1 : 2){
      for(z3 in 1 : 2){
        { vector[2] acc0;
          acc0 = rep_vector(0,2);
          for(z2_val in 1 : 2){
            acc0[z2_val] += m1[(z2_val - 1)*8+(z3-1)*4+(z4-1)*2+(z5-1)*1+1];

          }
          m2[(z3 - 1)*4+(z4-1)*2+(z5-1)*1+1] += log_sum_exp(acc0);
        }

      }

    }

  }
  m3 = rep_array(0, 4);
  for(z5 in 1 : 2){
    for(z4 in 1 : 2){
      { vector[2] acc0;
        acc0 = rep_vector(0,2);
        for(z3_val in 1 : 2){
          acc0[z3_val] += m2[(z3_val - 1)*4+(z4-1)*2+(z5-1)*1+1];

        }
        m3[(z4 - 1)*2+(z5-1)*1+1] += log_sum_exp(acc0);
      }

    }

  }
  m4 = rep_array(0, 2);
  for(z5 in 1 : 2){
    { vector[2] acc0;
      acc0 = rep_vector(0,2);
      for(z4_val in 1 : 2){
        acc0[z4_val] += m3[(z4_val - 1)*2+(z5-1)*1+1];

      }
      m4[z5] += log_sum_exp(acc0);
    }

  }
  m5 = 0;
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z5_val in 1 : 2){
      acc0[z5_val] += m4[(z5_val - 1)*1+1];

    }
    m5 += log_sum_exp(acc0);
  }


}
model {
  prior1 ~ beta(1, 1);
  prior2 ~ beta(1, 1);
  prior3 ~ beta(1, 1);
  prior4 ~ beta(1, 1);
  prior5 ~ beta(1, 1);
  target += m5;

}
generated quantities {
  int z1;
  int z2;
  int z3;
  int z4;
  int z5;
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z5_val in 1 : 2){
      acc0[z5_val] += m4[(z5_val - 1)*1+1];

    }
    z5 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z4_val in 1 : 2){
      acc0[z4_val] += m3[(z4_val - 1)*2+(z5-1)*1+1];

    }
    z4 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z3_val in 1 : 2){
      acc0[z3_val] += m2[(z3_val - 1)*4+(z4-1)*2+(z5-1)*1+1];

    }
    z3 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z2_val in 1 : 2){
      acc0[z2_val] += m1[(z2_val - 1)*8+(z3-1)*4+(z4-1)*2+(z5-1)*1+1];

    }
    z2 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z1_val in 1 : 2){
      acc0[z1_val] += bernoulli_lpmf(z1_val  - 1 | prior1);
      acc0[z1_val] += bernoulli_lpmf(z2  - 1 | prior2);
      acc0[z1_val] += bernoulli_lpmf(z3  - 1 | prior3);
      acc0[z1_val] += bernoulli_lpmf(z4  - 1 | prior4);
      acc0[z1_val] += bernoulli_lpmf(z5  - 1 | prior5);
      if(((((((z1_val + z2) + z3) + z4) + z5) - 5) > 0)){
        acc0[z1_val] += normal_lpdf(d1 | 135,8);
        acc0[z1_val] += normal_lpdf(d2 | 135,8);

      }
      else{
        acc0[z1_val] += normal_lpdf(d1 | 80,8);
        acc0[z1_val] += normal_lpdf(d2 | 80,8);

      }
    }
    z1 = categorical_logit_rng(acc0);
  }

}
