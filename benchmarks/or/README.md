# Conjugate Gaussians

This folder contains the needed files to replicate experiments in Section 2.1 in the [paper](https://arxiv.org/abs/2312.05706)

## Running HyBit

```bash
julia --project benchmarks/or/or.jl <number_of_genes>
```

## Sampling from WebPPL

Install WebPPL using instructions on this [link](https://github.com/probmods/webppl)
```bash
webppl conjugate_gaussians.wppl -- --s $((2**25)) --m MCMC >> result1MCMC.txt
webppl conjugate_gaussians.wppl -- --s $((2**25)) --m SMC >> result1SMC.txt
```