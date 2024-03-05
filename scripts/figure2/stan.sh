for (( i=1; i<=6; i++))
do
    timeout 1200s baselines/stan/or/or_$((5*$i)) sample num_warmup=1000 num_samples=1000000000 data file=baselines/stan/or/or.data.R output file=baselines/stan/or/or_$((5*$i)).csv
    /space/poorvagarg/cmdstan-2.28.2/bin/stansummary -s 8 baselines/stan/or/or_$((5*$i)).csv > baselines/stan/results_$((5*$i)).txt
    rm -rf baselines/stan/or/or_$((5*$i)).csv
done