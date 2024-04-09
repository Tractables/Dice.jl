for (( i=0; i<=12; i++))
do
    temp=$(($i + 4)) 
    ul=$(( temp > 12 ? 12 : temp))
    for (( j=0; j<=$ul; j++))
    do
        echo "bits $i pieces $((2**$j))"
	    timeout 9000s julia --project benchmarks/altermu2/altermu2_fig13.jl $i $((2**$j))
    done
done