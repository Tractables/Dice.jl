function for_between(f, f_between, xs)
    for (i, x) in enumerate(xs)
        f(x)
        if i < length(xs)
            f_between()
        end
    end
end

type_to_coq(x::L.Enum) = x.name

function to_coq(rs::RunState, p::GenerationParams{T}, prog::L.Program)::String where T
    prim_map, loc_map, tuple_tys, enums = check_tree(prog)

    vals = compute(rs.var_vals, values(rs.adnodes_of_interest))
    adnodes_vals = Dict(s => vals[adnode] for (s, adnode) in rs.adnodes_of_interest)

    matchid_to_cases = Dict()
    for (name, val) in adnodes_vals
        matchid, case = split(name, "%%")
        # println(case)
        case = if case == "" "tt" else "(" * join([value_to_coq(eval(Meta.parse(x))) for x in split(case, "%")], ", ") * ")" end
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

    tuple_to_struct(tys) = "Mk$(join([type_to_coq(ty) for ty in tys]))"

    function visit(x::L.Tuple)
        tys = Tuple(x.tys)
        a!("($(tuple_to_struct(tys)) ")
        for_between(() -> a!(" "), x.components) do component
            visit(component)
        end
        a!(")")

    end

    function visit(x::L.UnpackTuple)
        tys = Tuple(param.ty for param in x.bindings)
        a!("(let '($(tuple_to_struct(tys)) $(join([param.name for param in x.bindings], " "))) := ")
        visit(x.e)
        a!(" in\n")
        visit(x.body)
        a!(")")
    end

    function visit(x::L.ConstructEnum)
        a!(x.s)
    end

    function visit(x::L.MatchEnum)
        a!("match ")
        visit(x.scrutinee)
        a!(" with")
        for_indent(x.branches) do (ctor, body)
            o!("| $(ctor) => ")
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
        
        if haskey(matchid_to_cases, name)
            cases = matchid_to_cases[name]
            cases = sort(cases)
            for (name, w) in cases
                e!("| $(name) => $(w)")
            end
            if !isempty(dependents)
                e!("| _ => 500")
            end
        else
            e!("(* This match is dead code *) | _ => 500")
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
        e!(")" ^ (x.width * 2))
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

    function visit(x::L.ArbitraryBool)
        e!("arbitrary")
    end

    function visit(x::L.ArbitraryNat)
        e!("arbitrary")
    end

    function visit(x::L.ArbitraryZ)
        e!("arbitrary")
    end

    function visit(x::L.Function)
        recursive = any((y -> y isa L.Call && y.f == x.name), x)
        if recursive
            e!("Fixpoint $(x.name) ")
        else
            e!("Definition $(x.name) ")
        end
        for_between(() -> a!(" "), x.params) do param
            a!("($(param.name) : $(type_to_coq(param.ty)))")
        end
        a!(" : $(type_to_coq(x.ret_ty)) :=\n")
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

    e!(before)
    e!()

    for enum in enums
        e!("Inductive $(enum.name) :=")
        for_indent(enum.ctors) do ctor
            e!("| $(ctor)")
        end
        a!(".")
        e!()
    end

    for tys in tuple_tys
        s = join([type_to_coq(ty) for ty in tys])
        e!("Inductive Tup$(s) :=")
        with_indent() do
            e!("| Mk$(s) : ")
            for ty in tys
                a!("$(type_to_coq(ty)) -> ")
            end
            a!("Tup$(s).\n")
        end
    end


    visit(prog)

    e!(after)

    join(segments, "\n")
end