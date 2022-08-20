
import IfElse: ifelse

using DirectedAcyclicGraphs
import DirectedAcyclicGraphs: children, NodeType, DAG, Inner, Leaf

export Dist

"A probability distribution over values of type `T`"
abstract type Dist{T}  <: DAG end

Base.show(io::IO, x::Dist) = print(io, "$(typeof(x))@$(hash(x)÷ 10000000000000)")

include("distbool.jl")
include("distint.jl")
include("distsignedint.jl")
