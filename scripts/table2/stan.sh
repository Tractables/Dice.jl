for i in "weekend" "tug_of_war" "altermu2" "conjugate_gaussians2" "normal_mixture" "zeroone" "coinBias" "clickGraph" "trueskill" "clinicalTrial1" "clinicalTrial2"
do
    echo "Running $i"
    timeout 10s baselines/stan/$i/$i sample num_warmup=1000 num_samples=1000000000 data file=baselines/stan/$i/$i.data.R output file=baselines/stan/$i/$i.csv
    /space/poorvagarg/cmdstan-2.28.2/bin/stansummary -s 8 baselines/stan/$i/$i.csv > baselines/stan/$i/results_new.txt
    rm -rf baselines/stan/$i/$i.csv
done

for i in "pi" "spacex" "GPA" "addFun_sum" "addFun_max"
do
    echo "Running $i"
    timeout 10s baselines/stan/$i/$i sample num_warmup=1000 num_samples=1000000000 output file=baselines/stan/$i/$i.csv
    /space/poorvagarg/cmdstan-2.28.2/bin/stansummary -s 8 baselines/stan/$i/$i.csv > baselines/stan/$i/results_new.txt
    rm -rf baselines/stan/$i/$i.csv
done
