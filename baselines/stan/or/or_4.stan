data {
  real d1;
  real d2;

}
transformed data {
  real[2,2] m2;
  real[2] m3;
  real m4;
  m2 = rep_vector(0,[ 2, 2 ]);
  for(z4 in 1 : 2){
    for(z3 in 1 : 2){
      { vector[2] acc0;
        acc0 = rep_vector(0,2);
        for(z2_val in 1 : 2){
          acc0[z2_val] += m1[z2_val,z3,z4];

        }
        m2[[ 2, 2 ]] += log_sum_exp(acc0);
      }

    }

  }
  m3 = rep_vector(0,2);
  for(z4 in 1 : 2){
    { vector[2] acc0;
      acc0 = rep_vector(0,2);
      for(z3_val in 1 : 2){
        acc0[z3_val] += m2[z3_val,z4];

      }
      m3[z4] += log_sum_exp(acc0);
    }

  }
  m4 = 0;
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z4_val in 1 : 2){
      acc0[z4_val] += m3[z4_val];

    }
    m4 += log_sum_exp(acc0);
  }

}
parameters {
  real prior;

}
transformed parameters {
  real[2,2,2] m1;
  m1 = rep_vector(0,[ 2, 2, 2 ]);
  for(z4 in 1 : 2){
    for(z3 in 1 : 2){
      for(z2 in 1 : 2){
        { vector[2] acc0;
          acc0 = rep_vector(0,2);
          for(z1_val in 1 : 2){
            acc0[z1_val] += bernoulli_lpmf(z1_val | prior);
            acc0[z1_val] += bernoulli_lpmf(z2 | 0.5);
            acc0[z1_val] += bernoulli_lpmf(z3 | 0.5);
            acc0[z1_val] += bernoulli_lpmf(z4 | 0.5);
            if((((((z1_val + z2) + z3) + z4) - 4) > 0)){
              acc0[z1_val] += normal_lpdf(d1 | 1,1);
              acc0[z1_val] += normal_lpdf(d2 | 1,1);

            }
            else{
              acc0[z1_val] += normal_lpdf(d1 | -1,1);
              acc0[z1_val] += normal_lpdf(d2 | -1,1);

            }
          }
          m1[[ 2, 2, 2 ]] += log_sum_exp(acc0);
        }

      }

    }

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
      acc0[z4_val] += m3[z4_val];

    }
    z4 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z3_val in 1 : 2){
      acc0[z3_val] += m2[z3_val,z4];

    }
    z3 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z2_val in 1 : 2){
      acc0[z2_val] += m1[z2_val,z3,z4];

    }
    z2 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z1_val in 1 : 2){
      acc0[z1_val] += bernoulli_lpmf(z1_val | prior);
      acc0[z1_val] += bernoulli_lpmf(z2 | 0.5);
      acc0[z1_val] += bernoulli_lpmf(z3 | 0.5);
      acc0[z1_val] += bernoulli_lpmf(z4 | 0.5);
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
