for i in "pi" "addFun_sum" "addFun_max" "clickGraph" "clinicalTrial1" "clinicalTrial2" "coinBias" "conjugate_gaussians2" "zeroone_w2" "spacex" "trueskill" "weekend" "tug_of_war"
do
    echo "Running $i"
    timeout 1200s webppl baselines/webppl/$i/$i.wppl --require webppl-timeit -- --s $((2**16)) --m SMC >> baselines/webppl/$i/output_SMC_16_new.txt
done
for i in "normal_mixture_mu1" "normal_mixture_mu2" "normal_mixture_theta" "altermu2" 
do
    echo "Running $i"
    timeout 1200s webppl baselines/webppl/$i/$i.wppl --require webppl-timeit -- --s $((2**15)) --m SMC >> baselines/webppl/$i/output_SMC_15_new.txt
done
echo "Running GPA"
timeout 1200s webppl baselines/webppl/GPA/GPA.wppl --require webppl-timeit -- --s $((2**11)) --m SMC >> baselines/webppl/GPA/output_SMC_11_new.txt
echo "Running zeroone_w1"
timeout 1200s webppl baselines/webppl/zeroone_w1/zeroone_w1.wppl --require webppl-timeit -- --s $((2**11)) --m SMC >> baselines/webppl/zeroone_w1/output_SMC_11_new.txt