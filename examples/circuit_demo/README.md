# Examples for Integer Arithmetic

The examples in this directory demonstrate capabilities of Dice.jl to handle distributions over integers and integer arithmetic in probabilistic programs. In particular, we provide the following three examples with instructions to run these files from `Dice.jl` directory.

1. `adders.jl`: consists of an implementation of a half adder, full adder, and general addition circuit, as well as example calls for each.
```bash
# in Dice.jl directory
julia --project examples/circuit_demo/adders.jl
```
It outputs results of a half adder, a full adder and a three-bit addition circuit as follows:
```bash
One-bit half adder
DataStructures.DefaultOrderedDict{Any, Any, Float64}((true, false) => 0.5, (false, false) => 0.25, (false, true) => 0.25)

One-bit full adder
DataStructures.DefaultOrderedDict{Any, Any, Float64}((false, true) => 0.375, (true, false) => 0.375, (false, false) => 0.12500000000000003, (true, true) => 0.12500000000000003)

Adding two uniform distributions over integers 0 to 7
DataStructures.DefaultOrderedDict{Any, Any, Float64}(0 => 0.12500000000000003, 1 => 0.12500000000000003, 2 => 0.12500000000000003, 3 => 0.12500000000000003, 4 => 0.12500000000000003, 5 => 0.12500000000000003, 6 => 0.12500000000000003, 7 => 0.12500000000000003)
```


2. `state_change.jl`: demonstrates how Dice.jl can be used to record state changes in a probabilistic program. Specifically, we show how change in input distributions to an adder circuit can lead to change in the carry.
```bash
# in Dice.jl directory
julia --project examples/circuit_demo/state_change.jl
```

We expect the following output that records how often state of the `carry` changes.
```bash
Probability of state change
DataStructures.DefaultOrderedDict{Any, Any, Float64}(1 => 0.32031250000000006, 2 => 0.30468750000000006, 0 => 0.2578125, 3 => 0.11718749999999999)
Plot saved in ./examples/circuit_demo/state_change.png
```

3. `circuit_demo.jl`: implements the shared example of a hardware circuit and pushes uniform distributions through it. This example uses the machinery built into this system for integer arithmetic.
```bash
# in Dice.jl directory
julia --project examples/circuit_demo/circuit_demo.jl
```

We expect the following output:
```bash
Probabilities of pushing uniform distributions through the circuit
DataStructures.DefaultOrderedDict{Any, Any, Float64}(true => 0.7485364750027659, false => 0.25146352499723434)
```