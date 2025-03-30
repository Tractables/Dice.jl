export Nat, nat_ast_to_int

module Nat
    using Dice
    @type t = Z() | S(t)
end

function Nat.t(x::Unsigned)
    res = DistZero()
    for _ in 1:x
        res = DistSucc(res)
    end
    res
end

Base.zero(::Type{Nat.t}) = Nat.Z()

function Base.:(+)(x::Nat.t, y::Nat.t)
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
        branch_dict[:O]()
    else
        branch_dict[:S](sticky_sub(x, DistUInt32(1)))
    end
end
