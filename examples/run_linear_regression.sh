for ((w=2; w <=10; w++))
do
    for ((obs=1; obs<=20; obs++))
    do
        timeout 1800s julia --project examples/linear_regression.jl $((obs*10)) $((w))
    done
done