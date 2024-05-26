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

# Translate to a Coq program
function to_coq(rs::RunState, _::GenerationParams{T}, prog::L.Program)::String where T
    vals = compute(rs.var_vals, values(rs.adnodes_of_interest))
    adnodes_vals = Dict(s => vals[adnode] for (s, adnode) in rs.adnodes_of_interest)
    before, after = sandwich(T)

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
        segments[end] = segments[end] * s
    end
    e!(before)
    e!()

    function for_between(f, f_between, xs)
        for (i, x) in enumerate(xs)
            f(x)
            if i < length(xs)
                f_between()
            end
        end
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
        a!("(")
        for arg in x.args
            visit(arg)
        end
        a!(")")
    end

    function visit(x::L.Match)
        visit(x.scrutinee)
        for ((ctor, args), body) in x.branches
            visit(body)
        end
    end

    function visit(x::L.Call)
        for arg in x.args
            visit(arg)
        end
    end

    function visit(x::L.Lambda)
        visit(x.body)
    end

    function visit(x::L.Map)
        visit(x.f)
        visit(x.l)
    end

    function visit(x::L.BindGen)
        visit(x.gen)
        visit(x.body)
    end

    function visit(x::L.ReturnGen)
        visit(x.x)
    end

    function visit(x::L.OneOf)
        visit(x.default)
        visit(x.x)
    end

    function visit(x::L.Frequency)
        for (name, body) in x.branches
            visit(body)
        end
    end

    function visit(x::L.Backtrack)
        for (name, body) in x.branches
            visit(body)
        end
    end

    function visit(x::L.GenNat)
    end

    function visit(x::L.GenZ)
    end

    function visit(x::L.GenBool)
    end

    function visit(x::L.Function)
        visit(x.body)
    end

    function visit(x::L.Program)
        for f in x.functions
            visit(f)
        end
        visit(x.res)
    end
    visit(prog)

    e!(after)

    join(segments, "\n")
end
