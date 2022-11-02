# ul=$(($1 + 0))
for (( i=$1; i<=$2; i++))
do
    ul=$(($i + $4))
    for (( j=0; j<=$ul; j++))
    do
        for ((k=0; k<=$5; k++))
        do
	        timeout 9000s julia --project benchmarks/$3/$3.jl $i $((2**$j)) $k
        done
    done
done
