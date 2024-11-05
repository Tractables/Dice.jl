
# Arithmetic in Dice.jl

[![Unit Tests](https://github.com/Juice-jl/Dice.jl/workflows/Unit%20Tests/badge.svg)](https://github.com/Juice-jl/Dice.jl/actions?query=workflow%3A%22Unit+Tests%22+branch%3Amain)  [![codecov](https://codecov.io/gh/Tractables/Dice.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/Tractables/Dice.jl)

This is a Julia prototype implementation of the Dice probabilistic programming language with support for integers and integer arithmetic.
See [https://github.com/SHoltzen/dice](https://github.com/SHoltzen/dice) and ["Scaling Integer Arithmetic in Probabilistic Programs"](https://arxiv.org/abs/2307.13837).

* The microbenchmarks (Figure 5) are in `benchmarks/microbenchmarks/`
* The experiments (Table 1) are in `experiments/`

## Installation

Install Julia 1.7 or higher using [these instructions](https://julialang.org/downloads/platform/).

Clone the repository and start julia in project mode for current folder:
```bash
cd Dice.jl
julia --project
```

Install Dice and update dependencies (one can also use `precompile` or `build`):

```
] up
```

Press CTRL-C or backspace to exit from the pkg terminal and return to Julia REPL.

One can now run a program from the Julia REPL:
```julia
include("examples/graph_reachability.jl")
```

Or from the command line:
```
julia --project examples/graph_reachability.jl
```
