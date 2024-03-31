# HyBit

[![Unit Tests](https://github.com/Juice-jl/Dice.jl/workflows/Unit%20Tests/badge.svg)](https://github.com/Juice-jl/Dice.jl/actions?query=workflow%3A%22Unit+Tests%22+branch%3Amain)  [![codecov](https://codecov.io/gh/Juice-jl/Dice.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/Juice-jl/Dice.jl)

`HyBit` is a bit blasting based probabilistic programming system for discrete-continuous probabilistic programs. It is built on top of another probabilistic programming language Dice See [https://github.com/SHoltzen/dice](https://github.com/SHoltzen/dice).  

## Installation

Install Julia 1.8.5 or higher using [these instructions](https://julialang.org/downloads/platform/).

Then, install SymPy using the following command:

```bash
pip3 install sympy
```

Next, clone the repository and start julia in project mode for current folder:

```bash
cd Dice.jl
julia --project
```

In Julia REPL, then use the following command to install all the needed dependencies

```julia
using Pkg; Pkg.instantiate()
```

Once the Dice Julia package is instantiated, its inference algorithm and HyBit is ready to use.

## Quick Start

### Example: Discrete

Let's first start with a discrete probabilistic program. Imagine you have two coins `a` and `b` with probability of landing on heads as 0.4 and 0.6 respectively. You flip both the coins and see that one of them has landed heads. What is the probability that `a` lands heads?

```julia
using Dice
code = @dice begin
    a = flip(0.4)
    b = flip(0.6)
    observe(a | b)
    return a
end
@show pr(code)
```

We have this example written up in the file `examples/example1.jl`. It can be run as follows:

```bash
julia --project examples/example1.jl
```

And it should print the result as following showing that `a` is true with probability `0.526316`:

```bash
DataStructures.DefaultOrderedDict{Any, Any, Float64} with 2 entries:
  true  => 0.526316
  false => 0.473684
```

### Example: Discrete-Continuous

To see the use of HyBit to write discrete-continuous probabilistic programs, consider the following example. Here, we compute the probability of a random variable `a` being less than 0.

```julia
using Dice, Distributions
DFiP = DistFix{6, 2}
code = @dice begin
            a = bitblast(DFiP, Normal(0, 1), 4, -8.0, 8.0)
            b = a < DFiP(0.0)
            b
end
pr(code)
```

We have this example written up in the file `examples/example2.jl`. It can be run as follows:

```bash
julia --project examples/example2.jl
```

And it should print the result as following:

```bash
DataStructures.DefaultOrderedDict{Any, Any, Float64} with 2 entries:
  true  => 0.5
  false => 0.5
```

The Julia package Dice makes available the following constructs

* `@dice` macro that encapsulates the probabilistic program
* `observe()` to condition on a Boolean random variable being true.
* `DistFix{W, F}` as types to represent fixed point numbers with `W` bits, `F` bits being after the binary point. If the floating point numbers passed as an argument to `DistFix{W, F}` are outside the range $$[-2^{W - F - 1}, 2^{W - F - 1} - 2^{-F}]$$, one would encounter an error.
* `bitblast` to bitblast continuous density functions using linear pieces with the following signature.

```julia
function bitblast(::Type{DistFix{W,F}}, dist::ContinuousUnivariateDistribution, 
                  numpieces::Int, start::Float64, stop::Float64) where {W,F}
```

It also offers different probabilistic inference queries such as the following:

* `pr(code)` that computes the probability distribution of the returned types of `code`.
* `expectation(code)` computes the mean of the value returned by `code`
* `variance(code)` computes the variance of the value returned by `code`.

## More Examples

More examples can be found at the following directories:

* `test/` directory contains unit test cases for all the functions and data types implemented.
* `examples/` contains simple examples to get started with using Dice Julia package to write probabilistic programs.
* `benchmarks/` contains discrete-continuous probabilistic programs to get started with using bit blasting.  
