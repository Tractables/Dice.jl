
echo "Running pi"
timeout 1200s webppl baselines/webppl/pi/pi.wppl --require webppl-timeit -- --s $((2**25)) --m rejection >> baselines/webppl/pi/output_rejection_25_new.txt
echo "Running weekend"
timeout 1200s webppl baselines/webppl/weekend/weekend.wppl --require webppl-timeit -- --s $((2**24)) --m rejection >> baselines/webppl/weekend/output_rejection_24_new.txt
for i in "spacex" "addFun_max" "addFun_sum" "conjugate_gaussians2" "trueskill"
do
    echo "Running $i"
    timeout 1200s webppl baselines/webppl/$i/$i.wppl --require webppl-timeit -- --s $((2**22)) --m rejection >> baselines/webppl/$i/output_rejection_22_new.txt
done
echo "Running GPA"
timeout 1200s webppl baselines/webppl/GPA/GPA.wppl --require webppl-timeit -- --s $((2**10)) --m rejection >> baselines/webppl/GPA/output_rejection_10_new.txt
echo "Running tug_of_war"
timeout 1200s webppl baselines/webppl/tug_of_war/tug_of_war.wppl --require webppl-timeit -- --s $((2**19)) --m rejection >> baselines/webppl/tug_of_war/output_rejection_19_new.txt
for i in "altermu2" "normal_mixture_theta" "normal_mixture_mu1" "normal_mixture_mu2" "zeroone_w1"
do
    echo "Running $i"
    timeout 1200s webppl baselines/webppl/$i/$i.wppl --require webppl-timeit -- --s $((2**1)) --m rejection >> baselines/webppl/$i/output_rejection_1_new.txt
done
for i in "zeroone_w2" "coinBias"
do
    timeout 1200s webppl baselines/webppl/$i/$i.wppl --require webppl-timeit -- --s $((2**21)) --m rejection >> baselines/webppl/$i/output_rejection_21_new.txt
done
echo "Running clickGraph"
timeout 1200s webppl baselines/webppl/clickGraph/clickGraph.wppl --require webppl-timeit -- --s $((2**17)) --m rejection >> baselines/webppl/clickGraph/output_rejection_17_new.txt
echo "Running clinicalTrial1"
timeout 1200s webppl baselines/webppl/clinicalTrial1/clinicalTrial1.wppl --require webppl-timeit -- --s $((2**16)) --m rejection >> baselines/webppl/clinicalTrial1/output_rejection_16_new.txt
echo "Running clinicalTrial2"
timeout 1200s webppl baselines/webppl/clinicalTrial2/clinicalTrial2.wppl --require webppl-timeit -- --s $((2**20)) --m rejection >> baselines/webppl/clinicalTrial2/output_rejection_20_new.txt