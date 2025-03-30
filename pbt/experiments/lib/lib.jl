using Dice
using Dates
using Random

mutable struct RunState
    var_vals::Valuation
    adnodes_of_interest::Dict{String,ADNode}
    io::IO
    out_dir::String
    rng::AbstractRNG
    prim_map
    p
    coupled_ad_computer::ADComputer
end
RunState(
    var_vals, print_adnodes_of_interest, io, out_dir, rng, prim_map, p,
) = 
    RunState(
        var_vals, print_adnodes_of_interest, io, out_dir, rng, prim_map, p, 
        ADComputer(Valuation()),
    )

abstract type Workload end
abstract type STLC <: Workload end
abstract type BST <: Workload end
abstract type RBT <: Workload end
abstract type Bools{W} <: Workload end

module Nat
    using Dice
    t = DistUInt32
end

module Z
    using Dice
    t = DistInt32
end

# type_to_coq(::Type{DistUInt32}) = "nat"
type_to_coq(::Type{Nat.t}) = "nat"
type_to_coq(::Type{Z.t}) = "Z"

include("lang/definition.jl")
include("lang/interp.jl")
include("lang/sample.jl")
include("sandwiches.jl")
include("lang/to_coq.jl")
include("util.jl")
include("stlc.jl")
include("rbt.jl")
include("bst.jl")
include("derive.jl")

flatten = Iterators.flatten

include("be.jl")
