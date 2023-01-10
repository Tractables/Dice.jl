# Dice.jl

[![Unit Tests](https://github.com/Juice-jl/Dice.jl/workflows/Unit%20Tests/badge.svg)](https://github.com/Juice-jl/Dice.jl/actions?query=workflow%3A%22Unit+Tests%22+branch%3Amain)  [![codecov](https://codecov.io/gh/Juice-jl/Dice.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/Juice-jl/Dice.jl)

A Julia prototype implementation of the Dice probabilistic programming language.
See [https://github.com/SHoltzen/dice](https://github.com/SHoltzen/dice)


## Installation

Install Julia 1.7 or higher using [these instructions](https://julialang.org/downloads/platform/).

Clone the git repository:
```bash
git clone -b grammar_global_mgr https://github.com/Juice-jl/Dice.jl.git
```

Start julia in project mode for current folder:
```bash
cd Dice.jl
julia --project
```

Install Dice and update dependencies (one can also use `precompile` or `build`):

```julia
] up
```

Press CTRL-C or backspace to exit from the pkg terminal and return to Julia REPL.

One can now run a program from the Julia REPL:
```julia
include("examples/lingustics/grammar.jl")
```

Or from the command line:
```julia
julia --project examples/linguistics/grammar.jl
```

## Recommended reading order
See `examples/linguistics/tour.jl` for a quick start to Dice.jl.

Then, linguistics examples in order of increasing complexity are as follows. The
expected output of each is in a comment at the bottom of the file.
```
examples/linguistics/state_machine.jl
examples/linguistics/grammar.jl
examples/linguistics/parser.jl
```
