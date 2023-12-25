# Yao-Vehtari-Gelman Model

This folder contains the needed files to replicate experiments in Section 2.2 in the [paper](https://arxiv.org/abs/2312.05706)

## Running HyBit

```bash
julia --project benchmarks/multimodal.jl
```

## Sampling from Stan

```bash
wget https://github.com/stan-dev/cmdstan/releases/download/v2.28.2/cmdstan-2.28.2.tar.gz
tar -xvzf cmdstan-2.28.2.tar.gz
cd cmdstan-2.28.2
make build
../run.sh
```

## Sampling from WebPPL

Install WebPPL using instructions on this [link](https://github.com/probmods/webppl)
```bash
webppl multimodal.wppl -- --s $((2**20)) --m MCMC >> result1MCMC.txt
webppl multimodal.wppl -- --s $((2**20)) --m SMC >> result1SMC.txt
```

## Running AQUA

Install AQUA using instructions on this [link](https://github.com/uiuc-arc/AQUA/tree/master) and run it on `multimodal.stan`