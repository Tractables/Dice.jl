for i in {2..10}
do
    echo "running for length $i"
    julia --project luhn.jl $i >> dicejl_luhn.txt
done