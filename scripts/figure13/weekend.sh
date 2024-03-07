for (( i=0; i<=20; i++))
do
    ul=$(($i + 3))
    for (( j=0; j<=$ul; j++))
    do
        echo "bits $i pieces $((2**$j))"
	    timeout 9000s julia --project benchmarks/weekend/weekend_fig13.jl $i $((2**$j))
    done
done