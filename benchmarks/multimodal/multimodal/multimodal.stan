data {
	int<lower=0>  N;
    real y[N];
}
parameters {
	real mu1;
	real:q mu2;
}
model {
	mu1 ~ uniform(-16, 16);
	mu2 ~ uniform(-16, 16);
	for (n in 1:N) {
		target += log_mix(2.00/3, normal_lpdf(y[n]|mu1, 1), normal_lpdf(y[n]|mu2, 1));
	}
}
