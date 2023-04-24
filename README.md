# Dice.jl

[![Unit Tests](https://github.com/Juice-jl/Dice.jl/workflows/Unit%20Tests/badge.svg)](https://github.com/Juice-jl/Dice.jl/actions?query=workflow%3A%22Unit+Tests%22+branch%3Amain)  [![codecov](https://codecov.io/gh/Juice-jl/Dice.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/Juice-jl/Dice.jl)

A Julia prototype implementation of the Dice probabilistic programming language.
See [https://github.com/SHoltzen/dice](https://github.com/SHoltzen/dice)


## Installation

First install ```Julia1.8```, then follow the following instructions.

To setup Dice.jl, run the following commands in a terminal:
```
git clone https://github.com/Juice-jl/Dice.jl.git
cd Dice.jl
julia --project
] up
```
To exit from julia terminal, use the follwing command:
```
exit()
```

To execute an example file, any of the following methods can be used.

1. Run file in julia REPL: Execute follwing commands inside Dice directory
```
julia --project
include("examples/graph_reachability.jl")
```

2. Run the following command inside Dice directory
```
julia --project examples/graph_reachability.jl
```