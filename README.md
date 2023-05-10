# Dice.jl

[![Unit Tests](https://github.com/Juice-jl/Dice.jl/workflows/Unit%20Tests/badge.svg)](https://github.com/Juice-jl/Dice.jl/actions?query=workflow%3A%22Unit+Tests%22+branch%3Amain)  [![codecov](https://codecov.io/gh/Juice-jl/Dice.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/Juice-jl/Dice.jl)

A Julia prototype implementation of the Dice probabilistic programming language.
See [https://github.com/SHoltzen/dice](https://github.com/SHoltzen/dice)


## Installation

Install Julia 1.7 or higher using [these instructions](https://julialang.org/downloads/platform/).

Clone the repository and start Julia in project mode for current folder:
```bash
cd Dice.jl
julia --project
```

Press `]` to enter the pkg terminal. Update packages. 
```
up
```

While still in the pkg terminal, (**important for M1 Macs**), add the patched version of CUDD.
```
add https://github.com/rtjoa/CUDD.jl.git#m1compat
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
