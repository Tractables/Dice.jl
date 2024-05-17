function empty_stack(p)
    Tuple(0 for _ in 1:p.stack_size)
end

function update_stack_tail(p, stack_tail, loc)
    @assert loc != 0
    Tuple(
        if i == p.stack_size
            loc
        else
            stack_tail[i + 1]
        end
        for i in 1:p.stack_size
    )
end

function backtrack_for(rs, name, opts::Vector{Opt.T{T}})::Opt.T{T} where T
    first_some(T, shuffle_for(rs, name, opts))
end

function shuffle_for(rs, name, xs)
    # Hand-build shuffle for lengths 2 and 3
    @dice_ite if length(xs) == 2
        pr_var2 = register_weight!(rs, "$(name)_pr_var2")
        if flip(pr_var2)
            [xs[1], xs[2]]
        else
            [xs[2], xs[1]]
        end
    elseif length(xs) == 3
        var = register_weight!(rs, "$(name)_var")
        app = register_weight!(rs, "$(name)_app")
        val = register_weight!(rs, "$(name)_abs")
        if flip(var / (var + app + val))
            # var is first
            if flip(app / (app + val))
                [xs[1], xs[2], xs[3]]  # var app val
            else
                [xs[1], xs[3], xs[2]]  # var val app
            end
        elseif flip(app / (app + val))
            # app is first
            if flip(var / (var + val))
                [xs[2], xs[1], xs[3]]  # app var val
            else
                [xs[2], xs[3], xs[1]]  # app val var
            end
        else
            # val is first
            if flip(var / (var + app))
                [xs[3], xs[1], xs[2]]  # val var app
            else
                [xs[3], xs[2], xs[1]]  # val app var
            end
        end
    else
        error("todo: generic shuffle")
    end
end

# function frequency(xs)
#     sample_from(xs)
# end

function backtrack(xs)
    isempty(xs) && return DistNone()
    x = sample_from(xs)
    remove!(xs, x)
    backtrack(xs)
end

function first_some(::Type{T}, xs) where T
    isempty(xs) && return DistNone(T)
    x, rest = xs[1], @view xs[2:end]
    @dice_ite if matches(x, "Some")
        x
    else
        first_some(T, rest)
    end
end

# Manually curry so we can have type be first arg and use "do"
function map_(::Type{RetT}) where RetT
    function inner(f, l::List{T}) where T
        match(l, [
            "Nil" => () -> DistNil(RetT),
            "Cons" => (x, xs) -> DistCons(f(x), map_(RetT)(f, xs))
        ])
    end
end

function freq_flips(weights)
    weight_sum = last(weights)
    flips = Vector(undef, length(weights))
    for i in length(weights) - 1 : -1 : 1
        weight_sum += weights[i]
        flips[i] = flip(weights[i] / weight_sum)
    end
    flips
end

function freq_choose(xs, flips)
    res = last(xs)
    for i in length(xs) - 1 : -1 : 1
        res = @dice_ite if flips[i]
            xs[i]
        else
            res
        end
    end
    res
end

function frequency(weights_xs)
    weights, xs = [], []
    for (weight, x) in weights_xs
        push!(weights, weight)
        push!(xs,x)
    end
    freq_choose(xs, freq_flips(weights))
end

function frequency_for(rs, name, xs)
    weights = [register_weight!(rs, "$(name)_$(i)") for i in 1:length(xs)]
    frequency(collect(zip(weights, xs)))
end

function opt_stlc_str(ast)
    name, children = ast
    if name == :None
        "None"
    elseif name == :Some
        ast′, = children
        stlc_str(ast′)
    else
        error("Bad node $(name)")
    end
end

function save_metric_dist(filename, dist; io)
    open(filename, "w") do file
        println(file, "val\tprobability")
        for i in key_range(dist)
            println(file, "$(i)\t$(dist[i])")
        end
    end
    println(io, "Saved metric dist to $(filename).")
end

key_range(d) = minimum(keys(d)):maximum(keys(d))

function preview_distribution(e; full_dist)
    if full_dist
        println("Getting distribution of all exprs")
        @time dist = pr(e)
        for (k, pr) in dist
            println("pr: $(pr)")
            println(opt_stlc_str(k))
            println()
        end
    else
        println("A few sampled exprs:")
        for _ in 1:20
            expr = sample(e)
            println(opt_stlc_str(expr))
        end
    end
end

function save_samples(rs, filename, e; n_samples=200)
    open(filename, "w") do file
        a = ADComputer(rs.var_vals)
        for _ in 1:n_samples
            expr_dist = sample_as_dist(rs.rng, a, e)
            expr = Dice.frombits(expr_dist, Dict())
            diff_test_typecheck(expr_dist, expr)
            println(file, opt_stlc_str(expr))
            # typecheck_opt(expr)
        end
    end
    println(rs.io, "Saved samples to $(filename).")
end

function println_flush(io, args...)
    println(io, args...)
    flush(io)
end

function showln(io::IO, v)
    show(io, v)
    println(io)
    println(io)
    flush(io)
end

function cmd_out(cmd)
    io = IOBuffer()
    run(pipeline(cmd, stdout=io))
    String(take!(io))
end

thousandths(n) = if isnan(n) "nan" else Integer(round(n, digits=3) * 1000) end
hundredths(n) = if isnan(n) "nan" else Integer(round(n * 100)) end

global _soft_assert_ever_triggered = Ref(false)

function to_unquoted(e)
    io = IOBuffer()
    Base.show_unquoted(io, e)
    String(take!(io))
end

macro soft_assert(io, b, msg)
    src = "$(__source__.file):$(__source__.line)"
    b_s = to_unquoted(b)
    quote
        if !$(esc(b))
            global _soft_assert_ever_triggered[] = true
            for io in Set([$(esc(io)), stdout])
                println(io, "Assertion failed at $($src)")
                println(io, $b_s)
                println(io, $(esc(msg)))
            end
        end
    end
end
atexit() do
    if _soft_assert_ever_triggered[]
        println("WARNING: this program failed soft assertion(s)")
        exit(1)
    end
end

function register_weight!(rs, s; random_value=false)
    var = Var("$(s)_before_sigmoid")
    if !haskey(rs.var_vals, var) || rs.var_vals[var] == 0
        rs.var_vals[var] = 0
    else
        println("WARNING: not registering fresh weight for $(s)")
    end
    if random_value
        rs.var_vals[var] = inverse_sigmoid(rand(rs.rng))
    end
    weight = sigmoid(var)
    rs.adnodes_of_interest[s] = weight
    weight
end

function print_adnodes_of_interest(rs::RunState, s::String)
    println_flush(rs.io, "ADNodes of interest ($(s)):")
    vals = compute(rs.var_vals, values(rs.adnodes_of_interest))
    d = Dict(s => vals[adnode] for (s, adnode) in rs.adnodes_of_interest)
    showln(rs.io, d)
end

function println_loud(rs::RunState, x)
    for io in Set([rs.io, stdout])
        println_flush(io, x)
    end
end

println_loud(rs) = println_loud(rs, "")

function flip_for(rs, name, dependents)
    res = nothing
    support = support_mixed(dependents; as_dist=true)
    @assert !isempty(support)
    for dependents_vals in support
        t = join([string(x) for x in dependents_vals], "%")
        v = flip(register_weight!(rs, "$(name)%%$(t)"))
        if isnothing(res)
            res = v
        else
            res = @dice_ite if prob_equals(dependents, dependents_vals)
                v
            else
                res
            end
        end
    end
    res
end

function frequency_for(rs, name, dependents, casenames_xs)
    casenames = []
    xs = []
    for (casename, x) in casenames_xs
        push!(casenames, casename)
        push!(xs, x)
    end

    res = nothing
    support = support_mixed(dependents; as_dist=true)
    @assert !isempty(support)
    for dependents_vals in support
        t = join([string(x) for x in dependents_vals], "%")
        weights = [
            register_weight!(rs, "$(name)_$(casename)%%$(t)")
            for casename in casenames
        ]
        v = frequency(collect(zip(weights, xs)))
        if isnothing(res)
            res = v
        else
            res = @dice_ite if prob_equals(dependents, dependents_vals)
                v
            else
                res
            end
        end
    end
    res
end

function tocoq(i::Integer)
    "$(i)"
end

function tocoq(v::Tuple)
    if v == ()
        "tt"
    else
        "($(join([tocoq(x) for x in v], ", ")))"
    end
end


function collect_types(root_ty)
    to_visit = [root_ty]
    seen = Set([root_ty])
    tys = [root_ty]
    while !isempty(to_visit)
        ty = pop!(to_visit)
        for (ctor, params) in variants(ty)
            for param in params
                if param ∉ seen && hasmethod(variants, (Type{param},))
                    push!(seen, param)
                    push!(to_visit, param)
                    push!(tys, param)
                end
            end
        end
    end
    reverse!(tys) # top order

    type_ctor_parami_to_id = Dict()
    for ty in tys
        for (ctor, params) in variants(ty)
            for (parami, param) in enumerate(params)
                if param in tys
                    type_ctor_parami_to_id[(ty, ctor, parami)] = length(type_ctor_parami_to_id) + 1
                end
            end
        end
    end

    tys, type_ctor_parami_to_id
end

variants2(ty, exclude_recursive) = if exclude_recursive
    [
        (ctor, params)
        for (ctor, params) in variants(ty)
        if !(ty in params)
    ]
else
    variants(ty)
end

function generate(rs::RunState, p, track_return)
    tys, type_ctor_parami_to_id = collect_types(p.root_ty)
    type_to_gen = Dict()
    for ty in tys
        type_to_gen[ty] = (leaf::Bool, chosen_varianti::DistUInt32, size, stack_tail) -> begin
            @assert !leaf || size == -1
            prefix = if leaf "leaf_" elseif size == 0 "0_" else "" end 
            dependents = if leaf stack_tail else (size, stack_tail) end
            zero_case()::Bool = if leaf
                error("don't check zero_case() if leaf")
            else
                size == 0
            end

            res = nothing
            for (varianti, (ctor, params)) in enumerate(variants(ty))
                if leaf && ty in params
                    continue
                end
                param_variantis = frequency_for(rs, "$(prefix)_$(ty)_$(ctor)_variantis", dependents, [
                    "$(x)" => [DistUInt32(j) for j in x]
                    for x in Iterators.product([
                        [
                            j
                            for (j, (_, param_params)) in enumerate(variants(param))
                            if !(param == ty && zero_case() && ty in param_params)
                        ]
                        for param in params
                        if param ∈ tys
                    ]...)
                ])
                param_variantis_idx = 0
                alt = ctor([
                    if param ∈ tys
                        param_variantis_idx += 1
                        type_to_gen[param](
                            # leaf
                            param == ty && zero_case(),
                            # chosen variant
                            param_variantis[param_variantis_idx],
                            # size
                            if param == ty
                                if zero_case()
                                    (-1)
                                else
                                    size - 1
                                end
                            else
                                p.ty_sizes[param]
                            end,
                            # todo: include leaf/zero_case in call location
                            update_stack_tail(p, stack_tail, type_ctor_parami_to_id[(ty, ctor, parami)])
                        )
                    elseif param == AnyBool
                        flip_for(rs, "$(prefix)$(ty)_$(ctor)_$(parami)_true", dependents)
                    elseif param == DistUInt32
                         sum(
                            @dice_ite if flip_for(rs, "$(prefix)$(ty)_$(ctor)_$(parami)_num$(n)", dependents)
                                DistUInt32(n)
                            else
                                DistUInt32(0)
                            end
                            for n in twopowers(p.intwidth)
                        )
                    else
                        error()
                    end
                    for (parami, param) in enumerate(params)
                ]...)
                if isnothing(res)
                    res = alt
                else
                    res = @dice_ite if prob_equals(DistUInt32(varianti), chosen_varianti)
                        alt
                    else
                        res
                    end
                end
            end
            res
        end
    end
    init_varianti = frequency_for(rs, "init_$(p.root_ty)_varianti", ((),), [
        "$(i)" => DistUInt32(i)
        for i in 1:length(variants(p.root_ty))
    ])
    type_to_gen[p.root_ty](false, init_varianti, p.ty_sizes[p.root_ty], empty_stack(p))
end

to_coq(::Type{DistUInt32}) = "nat"
to_coq(::Type{DistInt32}) = "Z"
to_coq(::Type{AnyBool}) = "bool"

function sandwichjoin(pairs; middle, sep)
    ls = []
    rs = []
    for (l, r) in pairs
        push!(ls, l)
        push!(rs, r)
    end
    reverse!(rs)
    join(
        Iterators.flatten([
            ls, [middle], rs
        ]), sep
    )
end

function derived_to_coq(p, adnodes_vals, io)
    matchid_to_cases = Dict()
    for (name, val) in adnodes_vals
        matchid, case = split(name, "%%")
        case = if case == "" "tt" else "(" * join([tocoq(eval(Meta.parse(x))) for x in split(case, "%")], ", ") * ")" end
        val = hundredths(val)
        push!(get!(matchid_to_cases, matchid, []), (case, val))
    end

    tys, type_ctor_parami_to_id = collect_types(p.root_ty)

    workload = workload_of(typeof(p))

    stack_vars = ["(stack$(i) : nat)" for i in 1:p.stack_size]

    update_stack_vars(loc) = if p.stack_size == 0
        ""
    else
        join(stack_vars[2:end], " ") * " $(loc)"
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
        segments[end] = segments[end] * s
    end

    before, after = sandwich(workload)
    e!(before)
    e!()

    function for_indent(f, iter)
        indent += 1
        map(f, iter)
        indent -= 1
    end

    coq_tuple(names) = if isempty(names)
        "tt"
    else
        "($(join(names, ", ")))"
    end

    function ematch!(matchid, leaf)
        cases = matchid_to_cases[matchid]
        cases = sort(cases)
        if leaf
            e!("match $(coq_tuple(stack_vars)) with ")
        else
            e!("match (size, $(coq_tuple(stack_vars))) with ")
        end
        for (name, w) in cases
            e!("| $(name) => $(w)")
        end
        if !(leaf && isempty(stack_vars))
            e!("| _ => 500")
        end
        e!("end")
    end

    for_indent(tys) do ty
        o!("Inductive $(to_coq(ty))_leaf_ctor :=")
        for (ctor, params) in variants(ty)
            if !(ty in params)
                e!("| Ctor_leaf_$(ctor)")
            end
        end
        a!(".")
        e!()
    end
    sif(c, s) = if c s else "" end

    for_indent(tys) do ty
        o!("Inductive $(to_coq(ty))_ctor :=")
        for (ctor, _) in variants(ty)
            e!("| Ctor_$(ctor)")
        end
        a!(".")
        e!()
    end

    variantis_types_placeholder = "(* VARIANTIS TYPES GO HERE *)"
    e!(variantis_types_placeholder)
    variantis_types_needed = Set()

    join2(it, sep) = join(it, sep) * sep

    for leaf in [true, false]
        leaf_prefix = if leaf "leaf_" else "" end
        for_indent(tys) do ty
            if leaf
                o!("Definition")
            else
                o!("Fixpoint")
            end
            a!(" gen_$(leaf_prefix)$(to_coq(ty)) ")
            a!("(chosen_ctor : $(to_coq(ty))_$(leaf_prefix)ctor) ")
            leaf || a!("(size : nat) ")
            a!(join2(stack_vars, " "))
            a!(": G $(to_coq(ty)) :=")

            ty_variants = [
                (ctor, params)
                for (ctor, params) in variants(ty)
                if !(leaf && ty in params)
            ]
            need_freq = length(ty_variants) > 1

            leaf || e!("match size with")
            zero_cases = if leaf begin [true] end else [true, false] end
            for _zero_case in zero_cases
                zero_case() = if leaf
                    error("don't check zero_case() if leaf")
                else
                    _zero_case
                end

                prefix = if leaf "leaf_" elseif zero_case() "0_" else "" end
                if !leaf
                    indent += 1
                    if zero_case()
                        o!("| 0 =>")
                    else
                        o!("| S size' =>")
                    end
                end

                e!("match chosen_ctor with")
                for_indent(variants2(ty, leaf)) do (ctor, params)
                    o!("| Ctor_$(leaf_prefix)$(ctor) =>")
                    rparens_needed = 0
                    need_variantis = any(
                        param in tys
                        for param in params
                    )
                    variantis_types = [
                        "$(to_coq(param))_$(if param == ty && zero_case() "leaf_" else "" end)ctor"
                        for param in params
                        if param in tys
                    ]
                    if length(variantis_types) > 1
                        push!(variantis_types_needed, variantis_types)
                    end
                    variantis_struct = join(variantis_types, "_")
                    variantis_struct_ctor = if length(variantis_types) > 1
                        "Mk$(variantis_struct) "
                    else
                        ""
                    end

                    variantis_options = Iterators.product([
                        [
                            # If were generating ourself, and we have zero fuel, then don't choose another recursive constructor
                            (j, "Ctor_$(if param == ty && zero_case() "leaf_" else "" end)$(param_ctor)")
                            for (j, (param_ctor, param_params)) in enumerate(variants(param))
                            if !(param == ty && zero_case() && ty in param_params)
                        ]
                        for param in params
                        if param in tys
                    ]...)
                    if need_variantis
                        e!("bindGen (freq [")
                        for_indent(enumerate(variantis_options)) do (j, param_ctor_is_and_param_ctors)
                            param_ctor_is = []
                            param_ctors = []
                            for (a, b) in param_ctor_is_and_param_ctors
                                push!(param_ctor_is, a)
                                push!(param_ctors, b)
                            end

                            if length(variantis_options) == 1
                                e!("(* no alternatives, so lets just put this again *)")
                                e!("(")
                                indent += 1
                                ematch!("$(prefix)_$(ty)_$(ctor)_variantis_$(Tuple(param_ctor_is))", leaf)
                                a!(",")
                                e!("returnGen ($(variantis_struct_ctor)$(join(param_ctors, " ")))")
                                indent -= 1
                                e!(");")
                            end

                            e!("(")
                            indent += 1
                            ematch!("$(prefix)_$(ty)_$(ctor)_variantis_$(Tuple(param_ctor_is))", leaf)
                            a!(",")
                            e!("returnGen ($(variantis_struct_ctor)$(join(param_ctors, " ")))")
                            indent -= 1
                            if j < length(variantis_options)
                                e!(");")
                            else
                                e!(")")
                            end
                        end
                        e!("]) (fun param_variantis =>")
                        rparens_needed += 1
                        
                        e!("let '($(variantis_struct_ctor)$(join(["param$(parami)_ctor" for (parami, param) in enumerate(params) if param in tys], " "))) := param_variantis in")
                    end
                    for (parami, param) in enumerate(params)
                        if param == ty
                            e!("bindGen (gen_$(if zero_case() "leaf_" else "" end)$(to_coq(param))")
                            a!(" param$(parami)_ctor")
                            zero_case() || a!(" size'")
                            a!(" $(update_stack_vars(type_ctor_parami_to_id[(ty, ctor, parami)])))")
                            e!("(fun p$(parami) : $(to_coq(param)) =>")
                            rparens_needed += 1
                        elseif param ∈ tys
                            e!("bindGen (gen_$(to_coq(param))")
                            a!(" param$(parami)_ctor")
                            a!(" $(p.ty_sizes[param])")
                            a!(" $(update_stack_vars(type_ctor_parami_to_id[(ty, ctor, parami)])))")
                            e!("(fun p$(parami) : $(to_coq(param)) =>")
                            rparens_needed += 1
                        elseif param == AnyBool
                            e!("let weight_true :=")
                            ematch!("$(prefix)$(ty)_$(ctor)_$(parami)_true", leaf)
                            e!("in")
                            e!("bindGen (freq [")
                            e!("  (weight_true, returnGen true);")
                            e!("  (1000-weight_true, returnGen false)")
                            e!("]) (fun p$(parami) : $(to_coq(param)) =>")
                            rparens_needed += 1
                        elseif param == DistUInt32
                            for n in twopowers(p.intwidth)
                                e!("let weight_$(n) :=")
                                ematch!("$(prefix)$(ty)_$(ctor)_$(parami)_num$(n)", leaf)
                                e!("in")
                                e!("bindGen (freq [")
                                e!("  (weight_$(n), returnGen $(n));")
                                e!("  (1000-weight_$(n), returnGen 0)")
                                e!("]) (fun n$(n) : nat =>")
                                rparens_needed += 1
                            end
                            e!("let p$(parami) := $(join(["n$(n)" for n in twopowers(p.intwidth)], " + ")) in ")
                        else
                            error()
                        end
                    end
                    e!("returnGen ($(ctor) $(join(["p$(parami)" for parami in 1:length(params)], " ")))")
                    a!(")" ^ rparens_needed)
                end

                if !leaf
                    indent -= 1
                end
                e!("end")
            end
            if !leaf
                e!("end")
            end
            a!(".")
            e!()
        end
    end

    e!("Definition gSized :=")
    indent += 1
    e!("bindGen (freq [")
    indent += 1
    for_indent(enumerate(variants(p.root_ty))) do (i, (ctor, params))
        o!("(")
        matchid = "init_$(p.root_ty)_varianti_$(i)"
        cases = matchid_to_cases[matchid]
        cases = sort(cases)
        e!("match (tt) with ")
        for (name, w) in cases
            e!("| $(name) => $(w)")
        end
         e!("end")
        a!(",")
        e!("returnGen Ctor_$(ctor)")
        o!(")")
        if i < length(variants(p.root_ty))
            a!(";")
        end
    end
    indent -= 1
    e!("]) (fun init_ctor =>")
    e!("gen_$(to_coq(p.root_ty)) init_ctor $(p.ty_sizes[p.root_ty])$(" 0" ^ p.stack_size)")
    a!(").")
    indent -= 1
    e!()
    e!(after)
    result = join(segments, "\n")
    replace(result, "$(variantis_types_placeholder)" => join([
        begin
            variantis_struct = join(variantis_types,"_")
            "Inductive $(variantis_struct) :=
  | Mk$(variantis_struct) : $(join(variantis_types," -> ")) -> $(variantis_struct)."
        end
        for variantis_types in variantis_types_needed
    ], "\n"))
end
