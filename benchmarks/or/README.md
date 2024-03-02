# Logical Structure

This folder contains the needed files to replicate experiments in Section 2.1 in the [paper](https://arxiv.org/abs/2312.05706)


## Running HyBit

```bash
julia --project benchmarks/or/or.jl <number_of_genes>
```

## Running Psi

Install Psi using instructions on this [link](https://github.com/eth-sri/psi)

```
python3 baselines/psi/or/generate_or.py <number_of_genes> >> baselines/psi/or/or_<number_of_genes>.psi
timeout 1200s ./psi baselines/psi/or/or_<number_of_genes>.psi
```

## Running Stan

To run discrete-continuous benchmarks in Stan, we make use of [SlicStan](https://github.com/mgorinova/SlicStan). Run the folliwng command to generate a SlicStan file for the benchmark.

```bash
cd benchmarks/or/or
python3 or.py <number_of_genes>
dotnet run --from-file or_<number_of_genes>.txt > or_<number_of_genes>.stan #Run SlicStan on .txt file
python3 modify.py or_<number_of_genes>.stan
```

Once the Stan files have been generated, install Stan using the folliwng commands:

```bash
cd ..
wget https://github.com/stan-dev/cmdstan/releases/download/v2.28.2/cmdstan-2.28.2.tar.gz
tar -xvzf cmdstan-2.28.2.tar.gz
cd cmdstan-2.28.2
make build
```

Run Stan on the generated files as follows

```bash
make STAN_THREADS=true ../or/or_<number_of_genes>
timeout 1200s ../or/or_<number_of_genes> sample num_warmup=100 num_samples=1000000000 data file=../or/or.data.R output file=../or/or_samples_<number_of_genes>.csv
bin/stansummary -s 8 ../or/or_samples_<number_of_genes>.csv > ../or/results_<number_of_genes>.txt
```

## Sampling from WebPPL

1. Install WebPPL using instructions on this [link](https://github.com/probmods/webppl).
2. Install webppl-timeit utility using the instructions on this [link](https://github.com/stuhlmueller/webppl-timeit) 
3. Run the following commands.

```bash
cd benchmarks/or/or_webppl
mkdir or_<number_of_genes>
python3 generate_or.py <number_of_genes> > or_<number_of_genes>/or_<number_of_genes>.wppl
./run.sh <number_of_genes> SMC
./run.sh <number_of_genes> MCMC
```