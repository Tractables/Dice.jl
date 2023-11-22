export Nat, DistZero, DistSucc, nat_ast_to_int

struct Nat <: InductiveType end

function param_lists(::Type{Nat})
    [
        "Zero" => [],
        "Succ" => [DistI{Nat}],
    ]
end

DistZero()  = construct(Nat, "Zero", [])
DistSucc(x) = construct(Nat, "Succ", [x])

function DistI{Nat}(x)
    res = DistZero()
    for _ in 1:x
        res = DistSucc(res)
    end
    res
end

Base.zero(::Type{DistI{Nat}}) = DistZero()

function Base.:(+)(x::DistI{Nat}, y::DistI{Nat})
    match(y, [
        "Zero" => () -> x
        "Succ" => y′ -> DistSucc(x) + y′
    ])
end

function nat_ast_to_int(ast)
    name, children = ast
    if name == "Zero"
        0
    elseif name == "Succ"
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
        branch_dict["Zero"]()
    else
        branch_dict["Succ"](sticky_sub(x, DistUInt32(1)))
    end
end
