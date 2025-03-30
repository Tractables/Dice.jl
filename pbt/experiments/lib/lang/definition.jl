using DataStructures

module L
    using Dice: InductiveType
    # using DirectedAcyclicGraphs: Leaf, Inner
    import DirectedAcyclicGraphs: NodeType, DAG, children, Leaf, Inner

    abstract type Expr <: DAG end
    abstract type Typ end

    abstract type G{T} end

    struct Enum
        name::String
        ctors::Vector{String}
    end

    struct Param
        name::Symbol
        ty::Union{Type,Enum}
    end

    mutable struct Loc <: Expr
    end
    NodeType(::Type{Loc}) = Leaf()

    # Basic operations
    mutable struct Var <: Expr
        s::Symbol
    end
    NodeType(::Type{Var}) = Leaf()

    mutable struct Nat <: Expr
        x::Integer
        function Nat(x)
            @assert x >= 0
            new(x)
        end
    end
    NodeType(::Type{Nat}) = Leaf()

    mutable struct Z <: Expr
        x::Integer
    end
    NodeType(::Type{Z}) = Leaf()

    mutable struct Bool <: Expr
        x::Base.Bool
    end
    NodeType(::Type{Bool}) = Leaf()

    mutable struct NatAdd <: Expr
        xs::Vector{Expr}
    end
    NodeType(::Type{NatAdd}) = Inner()
    children(x::NatAdd) = x.xs

    mutable struct ZAdd <: Expr
        xs::Vector{Expr}
    end
    NodeType(::Type{ZAdd}) = Inner()
    children(x::ZAdd) = x.xs

    mutable struct Eq <: Expr
        x::Expr
        y::Expr
    end
    NodeType(::Type{Eq}) = Inner()
    children(x::Eq) = [x.x, x.y]

    mutable struct If <: Expr
        c::Expr
        t::Expr
        e::Expr
    end
    NodeType(::Type{If}) = Inner()
    children(x::If) = [x.c, x.t, x.e]

    mutable struct Construct <: Expr
        ctor::Main.Function
        args::Vector{Expr}
    end
    NodeType(::Type{Construct}) = Inner()
    children(x::Construct) = x.args

    mutable struct Match <: Expr
        scrutinee::Expr
        branches::Vector{Pair{Main.Tuple{Symbol,Vector{Symbol}},Expr}}
    end
    NodeType(::Type{Match}) = Inner()
    children(x::Match) = vcat([x.scrutinee], [
        body
        for ((ctor, args), body) in x.branches
    ])

    mutable struct ConstructEnum <: Expr
        enum::Enum
        s::String
        function ConstructEnum(enum, s)
            @assert s in enum.ctors "$(enum) $(s)"
            new(enum, s)
        end
    end
    NodeType(::Type{ConstructEnum}) = Leaf()

    mutable struct MatchEnum <: Expr
        enum::Enum
        scrutinee::Expr
        branches::Vector{Pair{String,Expr}}
        function MatchEnum(enum, scrutinee, branches)
            for (s, _) in branches
                @assert s in enum.ctors "$(enum) $(s)"
            end
            new(enum, scrutinee, branches)
        end
    end
    NodeType(::Type{MatchEnum}) = Inner()
    children(x::MatchEnum) = vcat([x.scrutinee], [
        body
        for (ctor, body) in x.branches
    ])

    mutable struct Call <: Expr
        f::String
        args::Vector{Expr}
    end
    NodeType(::Type{Call}) = Inner()
    children(x::Call) = x.args

    mutable struct Tuple <: Expr
        tys::Vector{Union{Type,Enum}}
        components::Vector{Expr}
    end
    NodeType(::Type{Tuple}) = Inner()
    children(x::Tuple) = x.components

    mutable struct UnpackTuple <: Expr
        e::Expr
        bindings::Vector{Param}
        body::Expr
    end
    NodeType(::Type{UnpackTuple}) = Inner()
    children(x::UnpackTuple) = [x.e, x.body]

    # Not first-class (doesn't subtype Expr).
    # They can capture values, so it'd be extra work to implement closures.
    mutable struct Lambda <: DAG
        params::Vector{Symbol}
        body::Expr
    end
    NodeType(::Type{Lambda}) = Inner()
    children(x::Lambda) = [x.body]

    mutable struct Map <: Expr
        dest_module::Module
        f::Lambda
        l::Expr # must be a dist that defines map, like ListExpr.t
    end
    NodeType(::Type{Map}) = Inner()
    children(x::Map) = [x.f, x.l]

    # Randomness
    mutable struct BindGen <: Expr
        gen::Expr
        var::Symbol
        body::Expr
    end
    NodeType(::Type{BindGen}) = Inner()
    children(x::BindGen) = [x.gen, x.body]

    mutable struct ReturnGen <: Expr
        x::Expr
    end
    NodeType(::Type{ReturnGen}) = Inner()
    children(x::ReturnGen) = [x.x]

    mutable struct OneOf <: Expr
        default::Expr
        x::Expr # must be a dist that defines map, like ListExpr.t
    end
    NodeType(::Type{OneOf}) = Inner()
    children(x::OneOf) = [x.default, x.x]

    mutable struct Frequency <: Expr
        dependents::Vector{Expr}
        branches::Vector{Pair{String,Expr}}
    end
    NodeType(::Type{Frequency}) = Inner()
    children(x::Frequency) = vcat(x.dependents, [body for (name, body) in x.branches])

    mutable struct Backtrack <: Expr
        dependents::Vector{Expr}
        none::Expr
        branches::Vector{Pair{String,Expr}}
    end
    NodeType(::Type{Backtrack}) = Inner()
    children(x::Backtrack) = vcat(x.dependents, [x.none], [body for (name, body) in x.branches])

    mutable struct GenNat <: Expr
        dependents::Vector{Expr}
        width::Unsigned
    end
    NodeType(::Type{GenNat}) = Inner()
    children(x::GenNat) = x.dependents

    mutable struct GenZ <: Expr
        dependents::Vector{Expr}
        width::Unsigned
    end
    NodeType(::Type{GenZ}) = Inner()
    children(x::GenZ) = x.dependents

    mutable struct GenBool <: Expr
        dependents::Vector{Expr}
    end
    NodeType(::Type{GenBool}) = Inner()
    children(x::GenBool) = x.dependents

    mutable struct ArbitraryBool <: Expr end
    NodeType(::Type{ArbitraryBool}) = Leaf()

    mutable struct ArbitraryNat <: Expr end
    NodeType(::Type{ArbitraryNat}) = Leaf()

    mutable struct ArbitraryZ <: Expr end
    NodeType(::Type{ArbitraryZ}) = Leaf()

    # Functions
    mutable struct Function <: DAG
        name::String
        params::Vector{Param}
        ret_ty::Type
        body::Expr
    end
    NodeType(::Type{Function}) = Inner()
    children(x::Function) = [x.body]

    mutable struct Program <: DAG
        functions::Vector{Function}
        res::Expr
    end
    NodeType(::Type{Program}) = Inner()
    children(x::Program) = vcat(x.functions, [x.res])
end

function twopowers(n)
    [2^(i-1) for i in 1:n]
end

function Base.show(io::IO, x::Union{L.Program,L.Function,L.Expr,L.Lambda})
    ty = typeof(x)
    show(io, ty)
    print(io, "(")
    for_between(() -> print(io, ", "), fieldnames(ty)) do field
        show(io, getfield(x, field))
    end
    print(io, ")")
end

using DirectedAcyclicGraphs: children, isinner
dumbprint(x) = [getfield(x, field) for field in fieldnames(typeof(x))]
function check_tree(prog)
    prim_map = Dict()
    loc_map = Dict()
    tuple_tys = Set()
    enum_names = Set()
    enums = Set()

    prim_cts = Dict(
        L.Frequency => 0,
        L.Backtrack => 0,
        L.GenNat => 0,
        L.GenZ => 0,
        L.GenBool => 0,
    )

    parent_of = Dict()
    seen = Set{Any}([prog])
    to_visit = Deque{Any}()
    push!(to_visit, prog)
    while !isempty(to_visit)
        x = popfirst!(to_visit)

        xty = typeof(x)
        if haskey(prim_cts, xty)
            prim_cts[xty] += 1
            prim_map[x] = "$(nameof(xty))$(prim_cts[xty])"
        end

        if x isa L.Loc
            loc_map[x] = length(loc_map) + 1
        end

        if x isa L.Tuple
            tys = Tuple(x.tys)
            push!(tuple_tys, tys)
        end

        if x isa L.ConstructEnum && !(x.enum.name in enum_names)
            push!(enum_names, x.enum.name)
            push!(enums, x.enum)
        end

        if isinner(x)
            for y in children(x)
                if y in seen
                    println("====")
                    println("duplicate:  $(y) $(dumbprint(y))")
                    println("second parent: $(x) $(dumbprint(x))")
                    println("first parent: $(parent_of[y]) $(dumbprint(parent_of[y]))")
                    error()
                end
                push!(seen, y)
                parent_of[y] = x
                push!(to_visit, y)
            end
        end
    end

    prim_map, loc_map, tuple_tys, enums
end

type_to_coq(::Type{L.G{T}}) where T = "G ($(type_to_coq(T)))"
