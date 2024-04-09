for (( i=0; i<=11; i++))
do
    temp=$(($i + 5)) 
    ul=$(( temp > 12 ? 12 : temp))
    for (( j=2; j<=$ul; j++))
    do
        echo "bits $i pieces $((2**$j))"
	    timeout 9000s julia --project benchmarks/spacex/spacex_fig13.jl $i $((2**$j))
    done
done