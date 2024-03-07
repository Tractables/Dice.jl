# echo "Running GPA"
# for (( i=1; i<=30; i++))
# do
#     timeout 1200s java -cp "target/aqua-1.0.jar:lib/storm-1.0.jar" aqua.analyses.AnalysisRunner /space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/GPA/GPA.template $((2**$i))
#     python3 /space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/aqua_data.py GPA >> /space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/GPA/results_new.txt
# done

# for j in "altermu2" "conjugate_gaussians" "normal_mixture" "zeroone" "coinBias"
for j in "normal_mixture" "zeroone"
do
    echo "Running $j"
    for (( i=1; i<=30; i++))
    do
        timeout 1200s java -cp "target/aqua-1.0.jar:lib/storm-1.0.jar" aqua.analyses.AnalysisRunner /space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/$j $((2**$i))
        python3 /space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/aqua_data.py $j >> /space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/$j/results_new.txt
    done
done