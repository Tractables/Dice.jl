# Dice.jl

[![Unit Tests](https://github.com/Juice-jl/Dice.jl/workflows/Unit%20Tests/badge.svg)](https://github.com/Juice-jl/Dice.jl/actions?query=workflow%3A%22Unit+Tests%22+branch%3Amain)  [![codecov](https://codecov.io/gh/Juice-jl/Dice.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/Juice-jl/Dice.jl)

A Julia prototype implementation of the Dice probabilistic programming language.
See [https://github.com/SHoltzen/dice](https://github.com/SHoltzen/dice)


## Installation

First install ```Julia1.8```, then follow the following instructions.

To setup Dice.jl, run the following commands in a terminal. This will create a copy of the Dice.jl directory and install necessary dependencies. 

```
git clone https://github.com/Juice-jl/Dice.jl.git
cd Dice.jl
julia --project
] up
```

To then exit the Julia terminal, use the following command:

```
exit()
```

To execute a Dice.jl file (in this case, the graph reachability example), the following methods can be used:

1. Run file in Julia REPL: Execute the following commands inside the Dice.jl directory
```
julia --project
include("examples/graph_reachability.jl")
```

2. Run the following command inside Dice directory
```
julia --project examples/graph_reachability.jl
```