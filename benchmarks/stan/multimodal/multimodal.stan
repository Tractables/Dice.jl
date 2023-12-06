data {
	int<lower=0>  N;
        real y[N];
}
parameters {
	real<lower=-16, upper=16> mu1;
	real<lower=-16, upper=16> mu2;
}
model {
	for (n in 1:N) {
		target += log_mix(2.00/3, normal_lpdf(y[n]|mu1, 1), normal_lpdf(y[n]|mu2, 1));
	}
}
