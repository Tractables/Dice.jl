cd ../../../cmdstan-2.28.2
make STAN_THREADS=true ../.julia/dev/Dice.jl/baselines/stan/$1/$1
timeout $2s ../.julia/dev/Dice.jl/baselines/stan/$1/$1 sample num_warmup=1000 num_samples=1000000000 output file=../.julia/dev/Dice.jl/baselines/stan/$1/$1.csv
bin/stansummary -s 8 ../.julia/dev/Dice.jl/baselines/stan/$1/$1.csv > ../.julia/dev/Dice.jl/baselines/stan/$1/results_$2.txt
rm -rf ../.julia/dev/Dice.jl/baselines/stan/$1/$1.csv
rm -rf ../.julia/dev/Dice.jl/baselines/stan/$1/$1.hpp