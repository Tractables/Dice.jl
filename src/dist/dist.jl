
using DirectedAcyclicGraphs
import DirectedAcyclicGraphs: children, NodeType, DAG, Inner, Leaf

export Dist, isdeterministic

# TODO make DirectedAcyclicGraphs.DAG a trait so we are not thrown off by multiple inheritance here
"A probability distribution over values of type `T`"
abstract type Dist{T}  <: DAG end

"Does the distribution have a deterministic value?"
isdeterministic(x) =
    true
    # isempty(tobits(x))

function Base.show(io::IO, x::Dist) 
    if isdeterministic(x)
        print(io, "$(typeof(x))($(frombits(x, nothing)))")
    else
        print(io, "$(typeof(x))@$(hash(x)÷ 10000000000000)")
    end
end

include("bool.jl")
include("misc.jl")
include("number/uint.jl")
include("number/int.jl")
include("number/fix.jl")
include("char.jl")
include("string.jl")
include("enum.jl")
include("vector.jl")
include("inductive/inductive.jl")
include("inductive/option.jl")
include("inductive/nat.jl")
include("inductive/list.jl")
