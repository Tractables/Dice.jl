# Dice.jl - With support for integers and continuous distributions

[![Unit Tests](https://github.com/Juice-jl/Dice.jl/workflows/Unit%20Tests/badge.svg)](https://github.com/Juice-jl/Dice.jl/actions?query=workflow%3A%22Unit+Tests%22+branch%3Amain)  [![codecov](https://codecov.io/gh/Juice-jl/Dice.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/Juice-jl/Dice.jl)

This is a Julia embedding for the probabilistic programming language Dice [https://github.com/SHoltzen/dice](https://github.com/SHoltzen/dice) with further support for integer distributions, integer arithmetic and continuous distributions. [[1, 2]](#1). The repository has been tested only on Linux operating system.

## Installation

Install Julia 1.8.5 using [these instructions](https://julialang.org/downloads/platform/). 

Then, install SymPy using the following command:

```bash
pip3 install sympy
```

Next, clone the repository and checkout to the `arithmetic-demo` branch.

```bash
git clone https://github.com/Tractables/Dice.jl.git -b arithmetic-demo
```

Then start julia in project mode for current folder:

```bash
cd Dice.jl
julia --project
```

<!-- If you are using MacOS on a machine with M1 chip, please use the following commands instead:

```bash
cd Dice.jl
julia --project -e "import Pkg;Pkg.add(url=\"https://github.com/rtjoa/CUDD.jl.git\",rev=\"m1compat\")"
julia --project
``` -->

In Julia REPL, then use the following command to install all the needed dependencies

```julia
using Pkg; Pkg.instantiate()
```

Once the Dice Julia package is instantiated, its inference algorithm is ready to use.

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
pr(code) = DataStructures.DefaultOrderedDict{Any, Any, Float64}(true => 0.5263157894736843, false => 0.47368421052631576)
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
pr(code) = DataStructures.DefaultOrderedDict{Any, Any, Float64}(false => 0.5, true => 0.5)
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
* `examples/` contains simple examples to get started with using Dice Julia package to write probabilistic programs.
* `benchmarks/` contains discrete-continuous probabilistic programs to get started with using bit blasting.  

## References
<a id="1">[1]</a> 
William X. Cao, Poorva Garg, Ryan Tjoa, Steven Holtzen, Todd Millstein, and Guy Van den Broeck. 2023. Scaling integer arithmetic in probabilistic programs. In Proceedings of the Thirty-Ninth Conference on Uncertainty in Artificial Intelligence (UAI '23), Vol. 216. JMLR.org, Article 25, 260–270.

<a id="2">[2]</a>
Poorva Garg, Steven Holtzen, Guy Van den Broeck, and Todd Millstein. 2024. Bit Blasting Probabilistic Programs. Proc. ACM Program. Lang. 8, PLDI, Article 182 (June 2024), 24 pages. https://doi.org/10.1145/3656412