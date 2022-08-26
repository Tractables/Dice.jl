# Dice.jl

[![Unit Tests](https://github.com/Juice-jl/Dice.jl/workflows/Unit%20Tests/badge.svg)](https://github.com/Juice-jl/Dice.jl/actions?query=workflow%3A%22Unit+Tests%22+branch%3Amain)  [![codecov](https://codecov.io/gh/Juice-jl/Dice.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/Juice-jl/Dice.jl)

A Julia prototype implementation of the Dice probabilistic programming language.
See [https://github.com/SHoltzen/dice](https://github.com/SHoltzen/dice)


### Installation

Install julia 1.7 or higher using the [link](https://julialang.org/downloads/platform/).

Clone the git repository using the following command:
```bash
git clone -b grammar_global_mgr https://github.com/Juice-jl/Dice.jl.git
```

Start julia in project mode for current folder, i.e.:
```bash
julia --project
```

Then can install Dice and update dependencies by doing (also can do `precompile` or `build`)

```julia
] up
```

Press CTRL-C to exit from the pkg terminal and return to julia command line
Examples for having distributions on parse trees, probabilistic grammars and finite state machines can be found in the folder examples/linguistics which can be run as follows:

```julia
	include(“examples/lingustics/grammar.jl”)
```

Other examples can be run as follows
```julia
  include("examples/pfa.jl")
```

Now can do `] status` to see what versions of dependencies we have (or for more details can look into the `Manifest.toml` file).

```julia
(Dice) pkg> status
     Project Dice v0.1.0
      Status `~/Dice.jl/Project.toml`
  [345a2cc7] CUDD v0.2.2
  [1e6dae5e] DirectedAcyclicGraphs v0.1.0
  [615f187c] IfElse v0.1.1
  [1914dd2f] MacroTools v0.5.9
```
