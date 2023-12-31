data {
    int N;
    vector[N] y;

}
parameters {
    vector<lower=-8, upper=8>[2] mu;
}
model {
    mu ~ uniform(-8.0,8.0);
    y ~ normal((mu[1] + mu[2]), 1.0);

}
