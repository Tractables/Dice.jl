# Examples for Integer Arithmetic

The examples in this directory demonstrate capabilities of Dice.jl to handle distributions over integers and integer arithmetic in probabilistic programs. In particular, we provide the following three examples:

1. `adders.jl`: consists of an implementation of a half adder, full adder, and general addition circuit, as well as example calls for each.

2. `state_change.jl`: demonstrates how Dice.jl can be used to record state changes in a probabilistic program. Specifically, we show how change in input distributions to an adder circuit can lead to change in the carry.

3. `circuit_demo.jl`: implements the shared example of a hardware circuit and pushes uniform distributions through it. This example uses the machinery built into this system for integer arithmetic.