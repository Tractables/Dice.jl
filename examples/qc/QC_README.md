# Learning generator probabilities in Dice

Once the installation (see [`README.md`](README.md)) is complete, see [`test/tours/tour_1_core.jl`](../../test/tours/tour_1_core.jl) for a quick start to Dice.jl. Then, see [`test/tours/tour_2_learning.jl`](test/tours/tour_2_learning.jl) for an introduction to learning probabilities with MLE in Dice.jl.

The following related programs are included. The expected output of each is in a comment at the bottom of the file.
- Generator for nat lists ([`examples/demo_natlist.jl`](../../examples/demo_natlist.jl))
  - Given a generator for nat lists with a hole dependent on size, chooses probabilities such that the list has uniform length.
- Generator for binary search trees ([`examples/demo_bst.jl`](../../examples/demo_bst.jl))
  - Given a generator for binary search trees with a hole dependent on size, chooses probabilities such that the tree has uniform depth.
  - 50 example generated BSTs are visible at [`examples/samples/bst.txt`](examples/samples/bst.txt)
- Generator for well-typed, simply-typed lambda calculus expressions ([`benchmarks`](benchmarks))
  - Configure and run [`benchmarks/main.jl`](benchmarks/main.jl)

Please note: the programs expected to run on this version of Dice.jl are the above examples and the tests. Other examples are known to be broken.
