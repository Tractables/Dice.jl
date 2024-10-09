list=("addFun_max" "addFun_sum" "altermu2" "clickGraph" "clinicalTrial1" "clinicalTrial2"
    "coinBias" "GPA" "normal_mixture" "pi" "spacex" "trueskill" "tug_of_war" "weekend" "zeroone")
for i in ${list[@]}
do
    julia --project benchmarks/$i/$i.jl
done
