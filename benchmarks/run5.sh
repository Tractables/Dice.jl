# ul=$(($1 + 0))
for (( i=$1; i<=$2; i++))
do
	timeout 1200s julia --project benchmarks/$3/$3.jl $i $4
done