for (( i=0; i<=20; i++))
do
    for (( j=2; j<=12; j++))
    do
	    timeout 2000s julia --project benchmarks/or/or.jl $1 $i $((2**$j))
    done
done