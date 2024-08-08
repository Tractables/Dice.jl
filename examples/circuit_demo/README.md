This folder contains three files: half_adder.jl, state_change.jl, and circuit_demo.jl. 

- half_adder.jl contains an implementation of a half adder, full adder, and 
    general addition circuit, as well as an example calls on each. 

- state_change.jl uses the functions from the previous file for an example problem: 
    Counting the number of times an internal carry will change for an adder circuit 
    consisting of three chained full adders, when the input distribution over integers 
    is changed. 

- circuit_demo.jl implements the given example circuit, by creating and doing computation
    on uniform random integers. This uses the machinery built into the PPL (our unsigned
    integer representation DistUInt, and implemented functions for arithmetic).