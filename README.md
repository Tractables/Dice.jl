# Dice.jl

[![Unit Tests](https://github.com/Juice-jl/Dice.jl/workflows/Unit%20Tests/badge.svg)](https://github.com/Juice-jl/Dice.jl/actions?query=workflow%3A%22Unit+Tests%22+branch%3Amain)  [![codecov](https://codecov.io/gh/Juice-jl/Dice.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/Juice-jl/Dice.jl)

A Julia prototype implementation of the Dice probabilistic programming language.
See [https://github.com/SHoltzen/dice](https://github.com/SHoltzen/dice)


## Installation

1. Install Julia 1.7 or higher using [these instructions](https://julialang.org/downloads/platform/).

2. Clone this repository and navigate to its root folder. **Check out branch `q12`**.

4. If on Apple Silicon, first add our patched version of CUDD:
```
julia --project -e "import Pkg;Pkg.add(url=\"https://github.com/rtjoa/CUDD.jl.git\",rev=\"m1compat\")"`
```

4. Then, to install Dice and update dependencies:
```
julia --project -e "import Pkg;Pkg.update()"
```

One can now run a program from the Julia REPL (which can be opened with `julia --project`).
```julia
include("examples/graph_reachability.jl")
```

Or from the command line:
```
julia --project examples/graph_reachability.jl
```

## Running tests

The following should run within 10 minutes:

```
julia --project test/runtests.jl
```
