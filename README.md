# Dice.jl

[![Unit Tests](https://github.com/Juice-jl/Dice.jl/workflows/Unit%20Tests/badge.svg)](https://github.com/Juice-jl/Dice.jl/actions?query=workflow%3A%22Unit+Tests%22+branch%3Amain)  [![codecov](https://codecov.io/gh/Juice-jl/Dice.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/Juice-jl/Dice.jl)

A Julia prototype implementation of the Dice probabilistic programming language.
See [https://github.com/SHoltzen/dice](https://github.com/SHoltzen/dice)


## Linguistics in Dice

Once the installation (instructions below) is complete, see [`examples/linguistics/tour.jl`](examples/linguistics/tour.jl) for a quick start to Dice.jl.

The following linguistics-related programs are included. The expected output of each is in a comment at the bottom of the file.
- Probabilistic state machine ([`examples/linguistics/state_machine.jl`](examples/linguistics/state_machine.jl))
  - Given a probabilistic finite state machine, finds the distribution over sentences in its language.
  - The length of considered sentences is bounded, and the probability that this bound is exceeded is also calculated.
- Probabilistic grammar ([`examples/linguistics/grammar.jl`](examples/linguistics/grammar.jl))
  - Given a probabilistic context-free grammar (rules are annotated with the probability that its LHS nonterminal will expand to it), finds the distribution over sentences it can generate, given that the sentence starts with a particular prefix.
  - The height of the considered sentences' parse trees is bounded, and the probability that this bound is exceeded is also calculated.
- Probabilistic parser ([`examples/linguistics/parser.jl`](examples/linguistics/parser.jl))
  - Given a probabilistic context-free grammar and sentence, finds the distribution over possible parse trees for the sentence.
  - The height of the considered parse trees is bounded, and the probability that this bound is exceeded is also calculated.

Beware that the programs expected to run on this version of Dice.jl are the examples listed above and the tests. Other examples are known to be broken.

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