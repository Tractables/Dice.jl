# Alea.jl

[![Unit Tests](https://github.com/Juice-jl/Dice.jl/workflows/Unit%20Tests/badge.svg)](https://github.com/Juice-jl/Dice.jl/actions?query=workflow%3A%22Unit+Tests%22+branch%3Amain)  [![codecov](https://codecov.io/gh/Tractables/Dice.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/Tractables/Dice.jl)

Alea is a probabilistic programming system built in Julia based on the discrete probabilistic programming language Dice. See [https://github.com/SHoltzen/dice](https://github.com/SHoltzen/dice).

This repository currently consists code for the following papers:

1. [Bit Blasting Probabilistic Programs.](https://dl.acm.org/doi/10.1145/3656412) Poorva Garg, Steven Holtzen, Guy Van den Broeck, Todd Millstein. PLDI 2024.

2. [Scaling Integer Arithmetic in Probabilistic Programs.](https://dl.acm.org/doi/10.5555/3625834.3625859) William X. Cao, Poorva Garg, Ryan Tjoa, Steven Holtzen, Todd Millstein, Guy Van den Broeck. UAI 2023.

## HyBit

`HyBit` is a bit blasting based probabilistic programming system for discrete-continuous probabilistic programs. It is built on top of another probabilistic programming language Dice See [https://github.com/SHoltzen/dice](https://github.com/SHoltzen/dice).  

## Installation

Install Julia 1.8.5 or higher using [these instructions](https://julialang.org/downloads/platform/).

Then, install SymPy and IRTools using the following command:

```bash
pip3 install sympy
```

Next, clone the repository and `cd` to the top-level directory.

> If on Apple Silicon, add our patched version of CUDD:
> ```
> julia --project -e "import Pkg;Pkg.add(url=\"https://github.com/rtjoa/CUDD.jl.git\",rev=\"m1compat\")"`
> ```

Then, to install and update dependencies:
```
julia --project -e "using Pkg; Pkg.instantiate()"
```

One can now run a program from the Julia REPL (which can be opened with `julia --project`).
The Alea inference algorithm and HyBit is ready to use.

## Quick Start

### Example: Discrete

Let's first start with a discrete probabilistic program. Imagine you have two coins `a` and `b` with probability of landing on heads as 0.4 and 0.6 respectively. You flip both the coins and see that one of them has landed heads. What is the probability that `a` lands heads?

```julia
using Alea
code = @alea begin
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
using Alea, Distributions
DFiP = DistFix{6, 2}
code = @alea begin
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

The Julia package Alea makes available the following constructs

* `@alea` macro that encapsulates the probabilistic program
* `observe()` to condition on a Boolean random variable being true.
* `DistFix{W, F}` as types to represent fixed point numbers with `W` bits, `F` bits being after the binary point. If the floating point numbers passed as an argument to `DistFix{W, F}` are outside the range $$[-2^{W - F - 1}, 2^{W - F - 1} - 2^{-F}]$$, one would encounter an error.
* `bitblast` to bitblast continuous density functions using linear pieces with the following signature.

```julia
function bitblast(::Type{DistFix{W,F}}, dist::ContinuousUnivariateDistribution, 
                  numpieces::Int, start::Float64, stop::Float64) where {W,F}
```

* 'general_gamma' to bitblast general gamma densities $$x^{\alpha}e^{\beta x}$$ soundly with the following signature

```julia
function general_gamma(::Type{DistFix{W, F}}, alpha::Int, beta::Float64, ll::Float64, ul::Float64) where {W, F}
```

It also offers different probabilistic inference queries such as the following:

* `pr(code)` that computes the probability distribution of the returned types of `code`.
* `expectation(code)` computes the mean of the value returned by `code`
* `variance(code)` computes the variance of the value returned by `code`.

## More Examples

More examples can be found at the following directories:

* `test/` directory contains unit test cases for all the functions and data types implemented.
* `examples/` contains simple examples to get started with using Alea Julia package to write probabilistic programs.
* `benchmarks/` contains discrete-continuous probabilistic programs to get started with using bit blasting.  
