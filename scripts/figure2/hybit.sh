for (( i=1; i<=10; i++))
do
    julia --project benchmarks/or/or.jl $((5*$i))
    echo "Completed $((5*$i))"
done