using Dice
using Dates
using Random

DistNat = DistUInt32

struct RunState
    var_vals::Valuation
    adnodes_of_interest::Dict{String,ADNode}
    io::IO
    out_dir::String
    rng::AbstractRNG
    prim_map
    p
end

include("lang.jl")
include("util.jl")
include("lruset/dist.jl")
include("lruset/generator.jl")
include("stlc.jl")
include("bst.jl")
include("derive.jl")
safedec(x::DistUInt{T}) where T = @dice_ite if prob_equals(x, DistUInt{T}(0)) DistUInt{T}(0) else x - DistUInt{T}(1) end

function tree_size(e::KVTree.t)
    match(e, [
        :E => () -> DistUInt32(0),
        :T => (l, k, v, r) -> DistUInt32(1) + tree_size(l) + tree_size(r),
    ])
end
include("rbt.jl")
flatten = Iterators.flatten

function value_to_coq(c::Color.t)
    @match c [
        Red() -> "R",
        Black() -> "B",
    ]
end
include("be.jl")
