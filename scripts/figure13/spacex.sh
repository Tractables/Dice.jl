for (( i=0; i<=11; i++))
do
    ul=$(($i + 5))
    for (( j=2; j<=$ul; j++))
    do
        echo "bits $i pieces $((2**$j))"
	    timeout 9000s julia --project benchmarks/spacex/spacex_fig13.jl $i $((2**$j))
    done
done