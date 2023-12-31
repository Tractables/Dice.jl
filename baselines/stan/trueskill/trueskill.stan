data{
    int N;
    int y[N];
}
parameters {
    real alice;
    real bob;
    real alice_perf;
    real bob_perf;
}
transformed parameters {
    real final = (alice_perf > bob_perf) ? 1 : 0;
}
model {
    alice ~ normal(5, 1);
    bob ~ normal(5, 1);

    alice_perf ~ normal(alice, 1);
    bob_perf ~ normal(bob, 1);
    for (n in 1:N) {
    	target += ((alice_perf > bob_perf) == y[n]) ? 1 : 0;
    }
}
