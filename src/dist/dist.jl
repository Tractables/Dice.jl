
using DirectedAcyclicGraphs
import DirectedAcyclicGraphs: children, NodeType, DAG, Inner, Leaf

export Dist

# TODO make DirectedAcyclicGraphs.DAG a trait so we are not thrown off by multiple inheritance here
"A probability distribution over values of type `T`"
abstract type Dist{T}  <: DAG end

Base.show(io::IO, x::Dist) = print(io, "$(typeof(x))@$(hash(x)÷ 10000000000000)")

include("bool.jl")
include("integer/uint.jl")
include("integer/int.jl")
include("fixedpoint.jl")
