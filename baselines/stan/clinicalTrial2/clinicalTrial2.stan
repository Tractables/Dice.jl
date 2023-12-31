data {
  int N;
  int controlGroup[N];
  int isEffective;
  int treatedGroup[N];

}
parameters {
  real<lower = 0, upper = 1> probIfTreated;
  real<lower = 0, upper = 1> probextra;
}
transformed parameters {
  real<lower = 0, upper = 1> probIfControl;
  
  vector[2] lp;
  lp = rep_vector(0, 2);
  for (isEffective_val in 1:2) {
  	lp[isEffective_val] += bernoulli_lpmf(isEffective_val - 1 | 0.5);
      	if((isEffective_val > 1)){
                probIfControl = probextra;
        	for(n in 1 : N){
          		lp[isEffective_val] += bernoulli_lpmf(controlGroup[n] | probIfControl);
          		lp[isEffective_val] += bernoulli_lpmf(treatedGroup[n] | probIfTreated);
		}
      	} else{
		probIfControl = probIfTreated;
        	for(n in 1 : N){
          		lp[isEffective_val] += bernoulli_lpmf(controlGroup[n] | probIfControl);
          		lp[isEffective_val] += bernoulli_lpmf(treatedGroup[n] | probIfTreated);
        }

      }
    }
  }
model {
  probIfTreated ~ uniform(0, 1);
  probextra ~ uniform(0, 1);

  target += isEffective ? lp[2] : lp[1];
}
