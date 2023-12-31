data {
    int N;
    int y[N];
}
parameters {
    real<lower=-5,upper=5> alice;
    real<lower=-5,upper=5> bob;
}
model {
    target += log_mix(0.33,  normal_lpdf(alice | 3,1), normal_lpdf(alice | 5, 1));
    target += log_mix(0.33,  normal_lpdf(bob | 3,1), normal_lpdf(bob | 5, 1));
    for (i in 1:N) {
        target += (((abs(alice) > abs(bob)) == y[i])? 1:0);
    }
}
