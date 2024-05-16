# Bit Blasting in the context of Probabilistic Circuits

**Assumptions** Y values are in the range [0, 256] and Co and Cg values are in the range [-128, 128] shifted to [0, 256] 

This directory consists of the files for preliminary experiments for bit blasting in the context of probabilistic circuits.

Clone the respository using the following command:

```bash
git clone -b pcs https://github.com/Tractables/Dice.jl.git
```

We further elaborate different files and experiments within them:

1. `generate_support.jl`: consists of code to generate all valid (Y, Co, Cg) values and store them in the file `support.txt`

2. `ycocg_bdd.jl`: consists of code to read valid (Y, Co, Cg) values and generate the BDD and dump it in dot file `ycocg.dot` 

3. `ycocg_pr.jl`: consists of code for sanity check of the constraint over (Y, Co, Cg) values. Since only $2^{24}$ values are valid out of $2^{29}$ possible values, we expect output `true` probability to be $\frac{1}{32}$ i.e. $0.03125$

4. `ycocg_mle.jl`: consists of code to compute the probability of valid (Y, Co, Cg) values given the maximum likelihood parameters for all bits in the file `mle_params.txt`.

