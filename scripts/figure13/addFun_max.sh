for (( i=0; i<=18; i++))
do
    temp=$(($i + 3)) 
    ul=$(( temp > 12 ? 12 : temp))
    for (( j=0; j<=$ul; j++))
    do
        echo "bits $i pieces $((2**$j))"
	    timeout 9000s julia --project benchmarks/addFun_max/addFun_max_fig13.jl $i $((2**$j))
    done
done