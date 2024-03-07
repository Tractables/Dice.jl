for i in "pi" "weekend" "spacex" "GPA" "tug_of_war" "altermu2" "conjugate_gaussians2" "normal_mixture_theta" "normal_mixture_mu1" "normal_mixture_mu2" "zeroone_w1" "zeroone_w2" "coinBias" "addFun_sum" "clickGraph" "trueskill" "clinicalTrial1" "clinicalTrial2" "addFun_max"
do
    echo "Running $i"
    julia --project benchmarks/$i/$i.jl 2 2
done
