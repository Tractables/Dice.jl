# ul=$(($1 + 0))
for (( i=$1; i<=$2; i++))
do
    ul=$(($i + $4))
    for (( j=0; j<=$ul; j++))
    do
	    timeout 2000s julia --project benchmarks/$3/$3.jl $i $((2**$j)) $5
    done
done

# ./run4.sh 0 20 or 7 5 