for i in "pi" "weekend"
do
    echo "Running $i"
    timeout 1200s /space/poorvagarg/webppl/webppl baselines/webppl/$i/$i.wppl --require webppl-timeit -- --s $((2**25)) --m MCMC >> baselines/webppl/$i/output_MCMC_25.txt
done
for i in "spacex" "addFun_max" "addFun_sum"
do
    echo "Running $i"
    timeout 1200s /space/poorvagarg/webppl/webppl baselines/webppl/$i/$i.wppl --require webppl-timeit -- --s $((2**22)) --m MCMC >> baselines/webppl/$i/output_MCMC_22.txt
done
timeout 1200s /space/poorvagarg/webppl/webppl baselines/webppl/GPA/GPA.wppl --require webppl-timeit -- --s $((2**13)) --m MCMC >> baselines/webppl/GPA/output_MCMC_13.txt
for i in "tug_of_war" "clickGraph" "clinicalTrial1" "clinicalTrial2" "coinBias" "trueskill"
do
    echo "Running $i"
    timeout 1200s /space/poorvagarg/webppl/webppl baselines/webppl/$i/$i.wppl --require webppl-timeit -- --s $((2**24)) --m MCMC >> baselines/webppl/$i/output_MCMC_24.txt
done
for i in "altermu2" "normal_mixture_theta" "normal_mixture_mu1" "normal_mixture_mu2" "conjugate_gaussians2" "zeroone_w2"
do
    echo "Running $i"
    timeout 1200s /space/poorvagarg/webppl/webppl baselines/webppl/$i/$i.wppl --require webppl-timeit -- --s $((2**23)) --m MCMC >> baselines/webppl/$i/output_MCMC_23.txt
done
echo "Running zeroone_w1"
timeout 1200s /space/poorvagarg/webppl/webppl baselines/webppl/zeroone_w1/zeroone_w1.wppl --require webppl-timeit -- --s $((2**1)) --m MCMC >> baselines/webppl/zeroone_w1/output_MCMC_1.txt