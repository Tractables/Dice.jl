module L
    using Dice: InductiveType

    abstract type Expr end

    abstract type G{T} end

    struct Param
        name::Symbol
        ty::Type
    end

    # Basic operations
    mutable struct Var <: Expr
        s::Symbol
    end

    mutable struct Nat <: Expr
        x::Unsigned
    end

    mutable struct Z <: Expr
        x::Integer
    end

    mutable struct Bool <: Expr
        x::Base.Bool
    end

    mutable struct NatAdd <: Expr
        xs::Vector{Expr}
    end

    mutable struct ZAdd <: Expr
        xs::Vector{Expr}
    end

    mutable struct Eq <: Expr
        x::Expr
        y::Expr
    end

    mutable struct If <: Expr
        c::Expr
        t::Expr
        e::Expr
    end
    mutable struct Construct <: Expr
        inductive_type::Type
        ctor::Symbol
        args::Vector{Expr}
    end

    mutable struct Match <: Expr
        scrutinee::Expr
        branches::Vector{Pair{Tuple{Symbol,Vector{Symbol}},Expr}}
    end

    mutable struct Call <: Expr
        f::String
        args::Vector{Expr}
    end

    # Not first-class (doesn't subtype Expr).
    # They can capture values, so it'd be extra work to implement closures.
    mutable struct Lambda
        params::Vector{Symbol}
        body::Expr
    end

    mutable struct Map <: Expr
        f::Lambda
        l::Expr # must be a dist that defines map, like ListExpr.T
    end

    # Randomness
    mutable struct BindGen <: Expr
        gen::Expr
        var::Symbol
        body::Expr
    end

    mutable struct ReturnGen <: Expr
        x::Expr
    end

    mutable struct OneOf <: Expr
        default::Expr
        x::Expr # must be a dist that defines map, like ListExpr.T
    end

    mutable struct Frequency <: Expr
        dependents::Vector{Expr}
        branches::Vector{Pair{String,Expr}}
    end

    mutable struct Backtrack <: Expr
        dependents::Vector{Expr}
        branches::Vector{Pair{String,Expr}}
    end

    mutable struct GenNat <: Expr
        dependents::Vector{Expr}
        width::Unsigned
    end

    mutable struct GenZ <: Expr
        dependents::Vector{Expr}
        width::Unsigned
    end

    mutable struct GenBool <: Expr
        dependents::Vector{Expr}
    end

    # Functions
    mutable struct Function
        name::String
        params::Vector{Param}
        ret_ty::Type
        body::Expr
    end
 
    mutable struct Program
        functions::Vector{Function}
        res::Expr
    end
end

# Interpret to a Dice dist
function to_dist(rs::RunState, prog::L.Program)::Dist
    @dice_ite if flip(0.5)
        OptExpr.Some(Expr.Bool(true))
    else
        OptExpr.Some(Expr.App(Expr.Bool(true), Expr.Bool(true)))
    end
end

to_coq(::Type{L.G{T}}) where T = "G ($(to_coq(T)))"

# Translate to a Coq program
function to_coq(rs::RunState, p::GenerationParams{T}, prog::L.Program)::String where T
    vals = compute(rs.var_vals, values(rs.adnodes_of_interest))
    adnodes_vals = Dict(s => vals[adnode] for (s, adnode) in rs.adnodes_of_interest)
    before, after = if p isa LangBespokeSTLCGenerator
        sandwichmaybestlc()
    else
        sandwich(T)
    end

    segments = []
    # Emit line
    indent = 0
    function e!(s=""; indent_=nothing)
        if isnothing(indent_)
            indent_  = indent
        end
        segment = if s == ""
            # don't indent empty line
            ""
        else
            "  " ^ indent_ * s
        end
        push!(segments, segment)
    end
    # Emit with outer indent
    o!(s) = e!(s, indent_=indent-1)
    # Append to last line
    function a!(s)
        @assert !isempty(segments)
        # if starting a new line, include indent
        if segments[end] == "" || segments[end][end] == '\n'
            s = "  " ^ indent * s
        end
        segments[end] = segments[end] * s
    end
    e!(before)
    e!()
    function for_indent(f, iter)
        indent += 1
        map(f, iter)
        indent -= 1
    end

    space() = a!(" ")

    function for_between(f, f_between, xs)
        for (i, x) in enumerate(xs)
            f(x)
            if i < length(xs)
                f_between()
            end
        end
    end

    function for_between_indent(f, f_between, xs)
        indent += 1
        for_between(f, f_between, xs)
        indent -= 1
    end


    function with_indent(f)
        indent += 1
        res = f()
        indent -= 1
        return res
    end

    function visit(x::L.Var)
        a!(string(x.s))
    end

    function visit(x::L.Nat)
        a!("$(x.x)")
    end

    function visit(x::L.Z)
        a!("$(x.x)%Z")
    end

    function visit(x::L.Bool)
        a!("$(x.x)")
    end

    function visit(x::L.NatAdd)
        a!("(")
        for_between(() -> a!(" + "), x.xs) do x
            visit(x)
        end
        a!(")")
    end

    function visit(x::L.ZAdd)
        a!("(")
        for_between(() -> a!(" + "), x.xs) do x
            visit(x)
        end
        a!(")%Z")
    end

    function visit(x::L.Eq)
        visit(x.x)
        a!(" = ")
        visit(x.y)
        a!("?")
    end

    function visit(x::L.If)
        e!("if ")
        visit(x.c)
        a!(" then\n")
        with_indent() do
            visit(x.t)
        end
        e!("else\n")
        with_indent() do
            visit(x.e)
        end
    end

    function visit(x::L.Construct)
        a!("($(x.ctor) ")
        for_between(space, x.args) do arg
            visit(arg)
        end
        a!(")")
    end

    function visit(x::L.Match)
        a!("match ")
        visit(x.scrutinee)
        a!(" with")
        for_indent(x.branches) do ((ctor, args), body)
            o!("| $(ctor) $(join([string(arg) for arg in args], " ")) => ")
            visit(body)
        end
        e!("end")
    end

    function visit(x::L.Call)
        a!("($(x.f) ")
        for_between(space, x.args) do arg
            visit(arg)
        end
        a!(")")
    end

    function visit(x::L.Lambda)
        e!("(fun $(join([string(param) for param in x.params], " ")) => ")
        with_indent() do
            visit(x.body)
        end
        a!(")")
    end

    function visit(x::L.Map)
        e!("(map ")
        visit(x.f)
        space()
        visit(x.l)
        a!(")")
    end

    function visit(x::L.BindGen)
        e!("(bindGen ")
        visit(x.gen)
        space()
        visit(L.Lambda([x.var], x.body))
        a!(")")
    end

    function visit(x::L.ReturnGen)
        e!("(returnGen ")
        visit(x.x)
        a!(")")
    end

    function visit(x::L.OneOf)
        e!("(oneOf_ ")
        visit(x.default)
        space()
        visit(x.x)
        a!(")")
    end

    function visit(x::L.Frequency)
        e!("(freq [")
        for_between_indent(() -> a!("; "), x.branches) do (name, body)
            e!("(1, ")
            visit(body)
            a!(")")
        end
        a!("])")
    end

    function visit(x::L.Backtrack)
        e!("(backtrack [")
        for_between_indent(() -> a!("; "), x.branches) do (name, body)
            e!("(1, ")
            visit(body)
            a!(")")
        end
        a!("])")
    end

    function visit(x::L.GenNat)
        e!("arbitrary")
    end

    function visit(x::L.GenZ)
        e!("arbitrary")
    end

    function visit(x::L.GenBool)
        e!("arbitrary")
    end

    function visit(x::L.Function)
        e!("Fixpoint $(x.name) ")
        for_between(() -> a!(" "), x.params) do param
            a!("($(param.name) : $(to_coq(param.ty)))")
        end
        a!(" : $(to_coq(x.ret_ty)) :=\n")
        with_indent() do
            visit(x.body)
        end
        a!(".")
        e!()
    end

    function visit(x::L.Program)
        for f in x.functions
            visit(f)
        end
        e!("Definition gSized :=\n")
        with_indent() do
            visit(x.res)
        end
        a!(".")
        e!()
    end
    visit(prog)

    e!(after)

    join(segments, "\n")
end
