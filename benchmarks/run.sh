# ul=$(($1 + 0))
for (( i=$1; i<=$2; i++))
do
	timeout 8000s julia --project benchmarks/$3/$3.jl $i
done