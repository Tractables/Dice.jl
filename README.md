# Dice.jl

[![Unit Tests](https://github.com/Juice-jl/Dice.jl/workflows/Unit%20Tests/badge.svg)](https://github.com/Juice-jl/Dice.jl/actions?query=workflow%3A%22Unit+Tests%22+branch%3Amain)  [![codecov](https://codecov.io/gh/Juice-jl/Dice.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/Juice-jl/Dice.jl)

A Julia prototype implementation of the Dice probabilistic programming language.
See [https://github.com/SHoltzen/dice](https://github.com/SHoltzen/dice)


### Installation

Until `DirectedAcyclicGraphs.jl` is registered in the julia repository (should happen within few days), you would need to install it manually by url, for example inside `Dice.jl` folder first run:

```bash
julia --project
```

Then can add the `DirectedAcyclicGraphs`, or put it in developement mode as follows:

```julia
] add https://github.com/Juice-jl/DirectedAcyclicGraphs.jl
```

```julia
] dev https://github.com/Juice-jl/DirectedAcyclicGraphs.jl
```
