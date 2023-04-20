# Dice.jl

[![Unit Tests](https://github.com/Juice-jl/Dice.jl/workflows/Unit%20Tests/badge.svg)](https://github.com/Juice-jl/Dice.jl/actions?query=workflow%3A%22Unit+Tests%22+branch%3Amain)  [![codecov](https://codecov.io/gh/Juice-jl/Dice.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/Juice-jl/Dice.jl)

A Julia prototype implementation of the Dice probabilistic programming language.
See [https://github.com/SHoltzen/dice](https://github.com/SHoltzen/dice)


## Learning generator probabilities in Dice

Once the installation (instructions below) is complete, see [`examples/qc/tour_1_core.jl`](examples/qc/tour_1_core.jl) for a quick start to Dice.jl. Then, see [`examples/qc/tour_2_learning.jl`](examples/qc/tour_2_learning.jl) for an introduction to learning probabilities with MLE in Dice.jl.

The following related programs are included. The expected output of each is in a comment at the bottom of the file.
- Generator for nat lists ([`examples/qc/demo_natlist.jl`](examples/qc/demo_natlist.jl))
  - Given a generator for nat lists with a hole dependent on size, chooses probabilities such that the list has uniform length.
- Generator for sorted nat lists ([`examples/qc/demo_sortednatlist.jl`](examples/qc/demo_sortednatlist.jl))
  - Given a generator for sorted nat lists with a hole dependent on size, chooses probabilities such that the list has uniform length.
- Generator for binary search trees ([`examples/qc/demo_bst.jl`](examples/qc/demo_bst.jl))
  - Given a generator for binary search trees with a hole dependent on size, chooses probabilities such that the tree has uniform depth.
  - 50 example generated BSTs are visible at [`examples/qc/samples/bst.txt`](examples/qc/samples/bst.txt)
- Generator for closed untyped lambda calculus expressions ([`examples/qc/demo_utlc.jl`](examples/qc/demo_utlc.jl))
  - Given a generator for UTLC exprs with a hole dependent on size, chooses probabilities such that the AST has near uniform depth
  - 50 example generated expressions are visible at [`examples/qc/samples/utlc.txt`](examples/qc/samples/utlc.txt).

Beware that the programs expected to run on this version of Dice.jl are the examples listed above and the tests. Other examples are known to be broken.

## Installation

Install Julia 1.7 or higher using [these instructions](https://julialang.org/downloads/platform/).

Clone the git repository:
```bash
git clone -b qc4 https://github.com/Juice-jl/Dice.jl.git
```

Start julia in project mode for current folder:
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
include("examples/qc/demo_sortednatlist.jl")
```

Or from the command line:
```
julia --project examples/qc/demo_sortednatlist.jl
```