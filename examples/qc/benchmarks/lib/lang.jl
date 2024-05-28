using DataStructures

module L
    using Dice: InductiveType
    # using DirectedAcyclicGraphs: Leaf, Inner
    import DirectedAcyclicGraphs: NodeType, DAG, children, Leaf, Inner

    abstract type Expr <: DAG end

    abstract type G{T} end

    struct Param
        name::Symbol
        ty::Type
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
        x::Unsigned
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
        branches::Vector{Pair{Tuple{Symbol,Vector{Symbol}},Expr}}
    end
    NodeType(::Type{Match}) = Inner()
    children(x::Match) = vcat([x.scrutinee], [
        body
        for ((ctor, args), body) in x.branches
    ])

    mutable struct Call <: Expr
        f::String
        args::Vector{Expr}
    end
    NodeType(::Type{Call}) = Inner()
    children(x::Call) = x.args

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
        l::Expr # must be a dist that defines map, like ListExpr.T
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
        x::Expr # must be a dist that defines map, like ListExpr.T
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

function for_between(f, f_between, xs)
    for (i, x) in enumerate(xs)
        f(x)
        if i < length(xs)
            f_between()
        end
    end
end

function Base.show(io::IO, x::Union{L.Program,L.Function,L.Expr,L.Lambda})
    ty = typeof(x)
    show(io, ty)
    print(io, "(")
    for_between(() -> print(io, ", "), fieldnames(ty)) do field
        show(getfield(x, field))
    end
    print(io, ")")
end

using DirectedAcyclicGraphs: children, isinner
dumbprint(x) = [getfield(x, field) for field in fieldnames(typeof(x))]
function check_tree(prog)
    prim_map = Dict()
    loc_map = Dict()

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

    prim_map, loc_map
end

Env = Dict{Symbol, Any}

# Interpret to a Dice dist
function interp(rs::RunState, prog::L.Program)
    prim_map, loc_map = check_tree(prog)

    function with_binding(env, from, to)
        env2 = copy(env)
        env2[from] = to
        env2
    end

    functions = Dict(
        f.name => f
        for f in prog.functions
    )

    function_results = Dict(
        f.name => []
        for f in prog.functions
    )

    function interp(env::Env, x::L.Var)
        env[x.s]
    end

    function interp(env::Env, x::L.Loc)
        DistUInt32(loc_map[x])
    end

    function interp(env::Env, x::L.Nat)
        DistUInt32(x.x)
    end

    function interp(env::Env, x::L.Z)
        DistInt32(x.x)
    end

    function interp(env::Env, x::L.Bool)
        x.x
    end

    function interp(env::Env, x::L.NatAdd)
        sum(
            interp(env, y)
            for y in x.xs
        )
    end

    function interp(env::Env, x::L.ZAdd)
        sum(
            interp(env, y)
            for y in x.xs
        )
    end

    function interp(env::Env, x::L.Eq)
        prob_equals(
            interp(env, x.x),
            interp(env, x.y),
        )
    end

    function interp(env::Env, x::L.If)
        @dice_ite if interp(env, x.c)
            interp(env, x.t)
        else
            interp(env, x.e)
        end
    end

    function interp(env::Env, x::L.Construct)
        x.ctor([interp(env, arg) for arg in x.args]...)
    end

    function interp(env::Env, x::L.Match)
        Dice.match(interp(env, x.scrutinee), [
            ctor => (args...) -> begin
                @assert length(args) == length(vars)
                env1 = copy(env)
                for (var, arg) in zip(vars, args)
                    env1[var] = arg
                end
                interp(env1, body)
            end
            for ((ctor, vars), body) in x.branches
        ])
    end

    function interp(env::Env, x::L.Call)
        f = functions[x.f]
        @assert length(f.params) == length(x.args)
        res = interp(
            Env(
                param.name => interp(env, arg)
                for (param, arg) in zip(f.params, x.args)
            ),
            f.body
        )
        push!(function_results[x.f], res)
        res
    end

    function interp(env::Env, x::L.Lambda)
        error("Lambdas should be interped by Map.")
    end

    function interp(env::Env, x::L.Map)
        @assert length(x.f.params) == 1
        prob_map(
            x.dest_module,
            y -> begin
                interp(with_binding(env, x.f.params[1], y), x.f.body)
            end,
            interp(env, x.l)
        )
    end

    function interp(env::Env, x::L.BindGen)
        # we're always in the monad. this is just a let
        interp(
            with_binding(env, x.var, interp(env, x.gen)),
            x.body
        )
    end

    function interp(env::Env, x::L.ReturnGen)
        # always already in the monad
        interp(env, x.x)
    end

    function interp(env::Env, x::L.OneOf)
        one_of(
            interp(env, x.default),
            interp(env, x.x),
        )
    end

    function interp(env::Env, x::L.Frequency)
        dependents = [interp(env, dependent) for dependent in x.dependents]
        frequency_for(rs, prim_map[x], dependents, [
            name => interp(env, body)
            for (name, body) in x.branches
        ])
    end

    function interp(env::Env, x::L.Backtrack)
        dependents = [interp(env, dependent) for dependent in x.dependents]
        backtrack_for(rs, prim_map[x], dependents, [
                name => interp(env, body)
                for (name, body) in x.branches
            ],
            interp(env, x.none)
        )
    end

    function interp(env::Env, x::L.GenNat)
        name = prim_map[x]
        dependents = [interp(env, dependent) for dependent in x.dependents]
        sum(
            @dice_ite if flip_for(rs, "$(name)_num$(n)", dependents)
                DistUInt32(n)
            else
                DistUInt32(0)
            end
            for n in twopowers(x.width)
        )
    end

    function interp(env::Env, x::L.GenZ)
        name = prim_map[x]
        dependents = [interp(env, dependent) for dependent in x.dependents]
        sum(
            @dice_ite if flip_for(rs, "$(name)_num$(n)", dependents)
                DistInt32(n)
            else
                DistInt32(0)
            end
            for n in twopowers(x.width)
        )
    end

    function interp(env::Env, x::L.GenBool)
        name = prim_map[x]
        dependents = [interp(env, dependent) for dependent in x.dependents]
        flip_for(rs, "$(name)_true", dependents)
    end

    res = interp(Env(), prog.res)

    res, prim_map, function_results
end

to_coq(::Type{L.G{T}}) where T = "G ($(to_coq(T)))"

# Translate to a Coq program
function to_coq(rs::RunState, p::GenerationParams{T}, prog::L.Program)::String where T
    prim_map, loc_map = check_tree(prog)

    vals = compute(rs.var_vals, values(rs.adnodes_of_interest))
    adnodes_vals = Dict(s => vals[adnode] for (s, adnode) in rs.adnodes_of_interest)

    matchid_to_cases = Dict()
    for (name, val) in adnodes_vals
        matchid, case = split(name, "%%")
        case = if case == "" "tt" else "(" * join([tocoq(eval(Meta.parse(x))) for x in split(case, "%")], ", ") * ")" end
        val = hundredths(val)
        push!(get!(matchid_to_cases, matchid, []), (case, val))
    end

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

    function visit(x::L.Loc)
        a!(string(loc_map[x]))
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
        a!("($(nameof(x.ctor)) ")
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

    coq_tuple(names) = if isempty(names)
        "tt"
    else
        "($(join(names, ", ")))"
    end

    function ematch!(name, dependents)
        a!("match (")
        if isempty(dependents)
            a!("tt")
        else
            for_between(() -> a!(", "), dependents) do dep
                visit(dep)
            end
        end
        a!(") with")
        
        cases = matchid_to_cases[name]
        cases = sort(cases)
        for (name, w) in cases
            e!("| $(name) => $(w)")
        end
        if !isempty(dependents)
            e!("| _ => 500")
        end
        e!("end")
    end
    
    function visit(x::L.Frequency)
        name = prim_map[x]
        if length(x.branches) == 1
            e!("(* $(name) (single-branch) *) ")
            visit(x.branches[1][2])
        else
            e!("(* $(name) *) (freq [")
            for_between_indent(() -> a!("; "), x.branches) do (brname, body)
                e!("(* $(brname) *) (")
                ematch!("$(name)_$(brname)", x.dependents)
                a!(",")
                visit(body)
                a!(")")
            end
            a!("])")
        end
    end

    function visit(x::L.Backtrack)
        name = prim_map[x]
        e!("(* $(name) *) (backtrack [")
        for_between_indent(() -> a!("; "), x.branches) do (brname, body)
            e!("((* $(brname) *)")
            ematch!("$(prim_map[x])_$(brname)", x.dependents)
            a!(",")
            visit(body)
            a!(")")
        end
        a!("])")
    end

    function visit(x::L.GenNat)
        name = prim_map[x]
        e!("(* $(name) *)")
        for n in twopowers(x.width)
            e!("(let _weight_$(n) := ")
            ematch!("$(name)_num$(n)", x.dependents)
            e!("in")
            e!("bindGen (freq [")
            e!("  (_weight_$(n), returnGen $(n));")
            e!("  (100-_weight_$(n), returnGen 0)")
            e!("]) (fun n$(n) =>")
        end
        e!("  returnGen ($(join(["n$(n)" for n in twopowers(x.width)], " + ")))")
        e!(")" ^ (x.width * 2))
    end

    function visit(x::L.GenZ)
        name = prim_map[x]
        e!("(* $(name) *)")
        for n in twopowers(x.width)
            e!("(let _weight_$(n) := ")
            ematch!("$(name)_num$(n)", x.dependents)
            e!("in")
            e!("bindGen (freq [")
            e!("  (_weight_$(n), returnGen $(n)%Z);")
            e!("  (100-_weight_$(n), returnGen 0%Z)")
            e!("]) (fun n$(n) =>")
        end
        e!("  returnGen ($(join(["n$(n)" for n in twopowers(x.width)], " + ")))%Z")
        e!(")" ^ (x.width * 2 + 1))
    end

    function visit(x::L.GenBool)
        name = prim_map[x]
        e!("(* $(name) *) (let _weight_true := ")
        ematch!("$(name)_true", x.dependents)
        e!("in")
        e!("freq [")
        e!("  (_weight_true, returnGen true);")
        e!("  (100-_weight_true, returnGen false)")
        e!("])")
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
