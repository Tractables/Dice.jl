ul=$(($1 + 10))
for (( i=0; i<=$ul; i++))
do
        echo $1
        echo $i
        echo $2
        julia --project normal_mixture.jl $1 $i $2
done
