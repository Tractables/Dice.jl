export Nat, nat_ast_to_int

module Nat
    using Dice
    import Dice: param_lists
    @inductive T Z() S(DistI{T})
end

function DistI{Nat.T}(x)
    res = DistZero()
    for _ in 1:x
        res = DistSucc(res)
    end
    res
end

Base.zero(::Type{DistI{Nat.T}}) = Nat.Z()

function Base.:(+)(x::DistI{Nat.T}, y::DistI{Nat.T})
    match(y, [
        "Z" => () -> x
        "S" => y′ -> Nat.S(x) + y′
    ])
end

function nat_ast_to_int(ast)
    name, children = ast
    if name == "Z"
        0
    elseif name == "S"
        ast′, = children
        1 + nat_ast_to_int(ast′)
    else
        error("Bad node")
    end
end

# Also allow uints to be matched on
function sticky_sub(x, y)
    @dice_ite if x < y
        DistUInt32(0)
    else
        x - y
    end
end

function Dice.match(x::DistUInt32, branches)
    branch_dict = Dict(branches)
    @dice_ite if prob_equals(x, DistUInt32(0))
        branch_dict["Z"]()
    else
        branch_dict["S"](sticky_sub(x, DistUInt32(1)))
    end
end
