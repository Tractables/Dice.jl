data {
    int N;
    int y[N];
}
parameters {
    real alice;
    real bob;
}
transformed parameters {
    vector[4] lp;
    real ans;
    lp[1] = log(1.0/9);
    lp[2] = log(2.0/9);
    lp[3] = log(2.0/9);
    lp[4] = log(4.0/9);
    for (i in 1:N) {
        lp[1] += ((alice - 2 < bob - 2) == y[i]) ? 1 : 0;
        lp[2] += ((alice - 2 < bob) == y[i]) ? 1 : 0;
        lp[3] += ((alice < bob - 2) == y[i]) ? 1 : 0;
        lp[4] += ((alice < bob) == y[i]) ? 1 : 0;
    }
    ans = 0;
    ans += (1.0/9)*((alice - 2 < bob - 2) ? 1 : 0);
    ans += (2.0/9)*((alice - 2 < bob) ? 1 : 0);
    ans += (2.0/9)*((alice < bob - 2) ? 1 : 0);
    ans += (4.0/9)*((alice < bob) ? 1 : 0);
}
model {
    alice ~ normal(5, 1);
    bob ~ normal(5, 1);
    target += log_sum_exp(lp);
}
