data {
  real d1;
  real d2;

}
parameters {
  real<lower=0, upper=1> prior1;
  real<lower=0, upper=1> prior10;
  real<lower=0, upper=1> prior2;
  real<lower=0, upper=1> prior3;
  real<lower=0, upper=1> prior4;
  real<lower=0, upper=1> prior5;
  real<lower=0, upper=1> prior6;
  real<lower=0, upper=1> prior7;
  real<lower=0, upper=1> prior8;
  real<lower=0, upper=1> prior9;

}
transformed parameters {
	real m1[512];
  m1 = rep_array(0, 512);
  for(z9 in 1 : 2){
    for(z8 in 1 : 2){
      for(z7 in 1 : 2){
        for(z6 in 1 : 2){
          for(z5 in 1 : 2){
            for(z4 in 1 : 2){
              for(z3 in 1 : 2){
                for(z2 in 1 : 2){
                  for(z10 in 1 : 2){
                    { vector[2] acc0;
                      acc0 = rep_vector(0,2);
                      for(z1_val in 1 : 2){
                        acc0[z1_val] += bernoulli_lpmf(z1_val  - 1 | prior1);
                        acc0[z1_val] += bernoulli_lpmf(z2  - 1 | prior2);
                        acc0[z1_val] += bernoulli_lpmf(z3  - 1 | prior3);
                        acc0[z1_val] += bernoulli_lpmf(z4  - 1 | prior4);
                        acc0[z1_val] += bernoulli_lpmf(z5  - 1 | prior5);
                        acc0[z1_val] += bernoulli_lpmf(z6  - 1 | prior6);
                        acc0[z1_val] += bernoulli_lpmf(z7  - 1 | prior7);
                        acc0[z1_val] += bernoulli_lpmf(z8  - 1 | prior8);
                        acc0[z1_val] += bernoulli_lpmf(z9  - 1 | prior9);
                        acc0[z1_val] += bernoulli_lpmf(z10  - 1 | prior10);
                        if((((((((((((z1_val + z2) + z3) + z4) + z5) + z6) + z7) + z8) + z9) + z10) - 10) > 0)){
                          acc0[z1_val] += normal_lpdf(d1 | 135,8);
                          acc0[z1_val] += normal_lpdf(d2 | 135,8);

                        }
                        else{
                          acc0[z1_val] += normal_lpdf(d1 | 80,8);
                          acc0[z1_val] += normal_lpdf(d2 | 80,8);

                        }
                      }
                      m1[(z10 - 1)*256+(z2-1)*128+(z3-1)*64+(z4-1)*32+(z5-1)*16+(z6-1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1] += log_sum_exp(acc0);
                    }

                  }

                }

              }

            }

          }

        }

      }

    }

  }

  real m10;
	real m2[256];
	real m3[128];
	real m4[64];
	real m5[32];
	real m6[16];
	real m7[8];
	real m8[4];
	real m9[2];
  m2 = rep_array(0, 256);
  for(z9 in 1 : 2){
    for(z8 in 1 : 2){
      for(z7 in 1 : 2){
        for(z6 in 1 : 2){
          for(z5 in 1 : 2){
            for(z4 in 1 : 2){
              for(z3 in 1 : 2){
                for(z10 in 1 : 2){
                  { vector[2] acc0;
                    acc0 = rep_vector(0,2);
                    for(z2_val in 1 : 2){
                      acc0[z2_val] += m1[(z10 - 1)*256+(z2_val-1)*128+(z3-1)*64+(z4-1)*32+(z5-1)*16+(z6-1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1];

                    }
                    m2[(z10 - 1)*128+(z3-1)*64+(z4-1)*32+(z5-1)*16+(z6-1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1] += log_sum_exp(acc0);
                  }

                }

              }

            }

          }

        }

      }

    }

  }
  m3 = rep_array(0, 128);
  for(z9 in 1 : 2){
    for(z8 in 1 : 2){
      for(z7 in 1 : 2){
        for(z6 in 1 : 2){
          for(z5 in 1 : 2){
            for(z4 in 1 : 2){
              for(z10 in 1 : 2){
                { vector[2] acc0;
                  acc0 = rep_vector(0,2);
                  for(z3_val in 1 : 2){
                    acc0[z3_val] += m2[(z10 - 1)*128+(z3_val-1)*64+(z4-1)*32+(z5-1)*16+(z6-1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1];

                  }
                  m3[(z10 - 1)*64+(z4-1)*32+(z5-1)*16+(z6-1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1] += log_sum_exp(acc0);
                }

              }

            }

          }

        }

      }

    }

  }
  m4 = rep_array(0, 64);
  for(z9 in 1 : 2){
    for(z8 in 1 : 2){
      for(z7 in 1 : 2){
        for(z6 in 1 : 2){
          for(z5 in 1 : 2){
            for(z10 in 1 : 2){
              { vector[2] acc0;
                acc0 = rep_vector(0,2);
                for(z4_val in 1 : 2){
                  acc0[z4_val] += m3[(z10 - 1)*64+(z4_val-1)*32+(z5-1)*16+(z6-1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1];

                }
                m4[(z10 - 1)*32+(z5-1)*16+(z6-1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1] += log_sum_exp(acc0);
              }

            }

          }

        }

      }

    }

  }
  m5 = rep_array(0, 32);
  for(z9 in 1 : 2){
    for(z8 in 1 : 2){
      for(z7 in 1 : 2){
        for(z6 in 1 : 2){
          for(z10 in 1 : 2){
            { vector[2] acc0;
              acc0 = rep_vector(0,2);
              for(z5_val in 1 : 2){
                acc0[z5_val] += m4[(z10 - 1)*32+(z5_val-1)*16+(z6-1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1];

              }
              m5[(z10 - 1)*16+(z6-1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1] += log_sum_exp(acc0);
            }

          }

        }

      }

    }

  }
  m6 = rep_array(0, 16);
  for(z9 in 1 : 2){
    for(z8 in 1 : 2){
      for(z7 in 1 : 2){
        for(z10 in 1 : 2){
          { vector[2] acc0;
            acc0 = rep_vector(0,2);
            for(z6_val in 1 : 2){
              acc0[z6_val] += m5[(z10 - 1)*16+(z6_val-1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1];

            }
            m6[(z10 - 1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1] += log_sum_exp(acc0);
          }

        }

      }

    }

  }
  m7 = rep_array(0, 8);
  for(z9 in 1 : 2){
    for(z8 in 1 : 2){
      for(z10 in 1 : 2){
        { vector[2] acc0;
          acc0 = rep_vector(0,2);
          for(z7_val in 1 : 2){
            acc0[z7_val] += m6[(z10 - 1)*8+(z7_val-1)*4+(z8-1)*2+(z9-1)*1+1];

          }
          m7[(z10 - 1)*4+(z8-1)*2+(z9-1)*1+1] += log_sum_exp(acc0);
        }

      }

    }

  }
  m8 = rep_array(0, 4);
  for(z9 in 1 : 2){
    for(z10 in 1 : 2){
      { vector[2] acc0;
        acc0 = rep_vector(0,2);
        for(z8_val in 1 : 2){
          acc0[z8_val] += m7[(z10 - 1)*4+(z8_val-1)*2+(z9-1)*1+1];

        }
        m8[(z10 - 1)*2+(z9-1)*1+1] += log_sum_exp(acc0);
      }

    }

  }
  m9 = rep_array(0, 2);
  for(z10 in 1 : 2){
    { vector[2] acc0;
      acc0 = rep_vector(0,2);
      for(z9_val in 1 : 2){
        acc0[z9_val] += m8[(z10 - 1)*2+(z9_val-1)*1+1];

      }
      m9[z10] += log_sum_exp(acc0);
    }

  }
  m10 = 0;
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z10_val in 1 : 2){
      acc0[z10_val] += m9[(z10_val - 1)*1+1];

    }
    m10 += log_sum_exp(acc0);
  }


}
model {
  prior1 ~ beta(1, 1);
  prior2 ~ beta(1, 1);
  prior3 ~ beta(1, 1);
  prior4 ~ beta(1, 1);
  prior5 ~ beta(1, 1);
  prior6 ~ beta(1, 1);
  prior7 ~ beta(1, 1);
  prior8 ~ beta(1, 1);
  prior9 ~ beta(1, 1);
  prior10 ~ beta(1, 1);
  target += m10;

}
generated quantities {
  int z1;
  int z10;
  int z2;
  int z3;
  int z4;
  int z5;
  int z6;
  int z7;
  int z8;
  int z9;
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z10_val in 1 : 2){
      acc0[z10_val] += m9[(z10_val - 1)*1+1];

    }
    z10 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z9_val in 1 : 2){
      acc0[z9_val] += m8[(z10 - 1)*2+(z9_val-1)*1+1];

    }
    z9 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z8_val in 1 : 2){
      acc0[z8_val] += m7[(z10 - 1)*4+(z8_val-1)*2+(z9-1)*1+1];

    }
    z8 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z7_val in 1 : 2){
      acc0[z7_val] += m6[(z10 - 1)*8+(z7_val-1)*4+(z8-1)*2+(z9-1)*1+1];

    }
    z7 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z6_val in 1 : 2){
      acc0[z6_val] += m5[(z10 - 1)*16+(z6_val-1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1];

    }
    z6 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z5_val in 1 : 2){
      acc0[z5_val] += m4[(z10 - 1)*32+(z5_val-1)*16+(z6-1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1];

    }
    z5 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z4_val in 1 : 2){
      acc0[z4_val] += m3[(z10 - 1)*64+(z4_val-1)*32+(z5-1)*16+(z6-1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1];

    }
    z4 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z3_val in 1 : 2){
      acc0[z3_val] += m2[(z10 - 1)*128+(z3_val-1)*64+(z4-1)*32+(z5-1)*16+(z6-1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1];

    }
    z3 = categorical_logit_rng(acc0);
  }
  { vector[2] acc0;
    acc0 = rep_vector(0,2);
    for(z2_val in 1 : 2){
      acc0[z2_val] += m1[(z10 - 1)*256+(z2_val-1)*128+(z3-1)*64+(z4-1)*32+(z5-1)*16+(z6-1)*8+(z7-1)*4+(z8-1)*2+(z9-1)*1+1];

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
      acc0[z1_val] += bernoulli_lpmf(z6  - 1 | prior6);
      acc0[z1_val] += bernoulli_lpmf(z7  - 1 | prior7);
      acc0[z1_val] += bernoulli_lpmf(z8  - 1 | prior8);
      acc0[z1_val] += bernoulli_lpmf(z9  - 1 | prior9);
      acc0[z1_val] += bernoulli_lpmf(z10  - 1 | prior10);
      if((((((((((((z1_val + z2) + z3) + z4) + z5) + z6) + z7) + z8) + z9) + z10) - 10) > 0)){
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
