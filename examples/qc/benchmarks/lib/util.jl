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
    "($(join([tocoq(x) for x in v], ", ")))"
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

    type_ctor_to_id = Dict()
    for ty in tys
        for (ctor, _) in variants(ty)
            type_ctor_to_id[(ty, ctor)] = length(type_ctor_to_id)
        end
    end

    tys, type_ctor_to_id
end

function generate(rs::RunState, p, track_return)
    tys, type_ctor_to_id = collect_types(p.root_ty)
    type_to_gen = Dict()
    for ty in tys
        type_to_gen[ty] = (size, stack_tail) -> begin
            zero_prefix = if size == 0 "0_" else "" end 
            dependents = (size, stack_tail)
            frequency_for(rs,  "$(zero_prefix)$(ty)_variant", dependents, [
                "$(ctor)" => ctor([
                    if param == ty
                        # TODO: special-case enum like types
                        # TODO: if recursing, pass values of sibling *enumlikes*
                        type_to_gen[param](
                            size - 1,
                            update_stack_tail(p, stack_tail, type_ctor_to_id[(ty, ctor)])
                        )
                    elseif param ∈ tys
                        # TODO: special-case enum like types
                        type_to_gen[param](
                            p.ty_sizes[param],
                            update_stack_tail(p, stack_tail, type_ctor_to_id[(ty, ctor)])
                        )
                    elseif param == AnyBool
                        flip_for(rs, "$(zero_prefix)$(ty)_$(ctor)_$(i)", dependents)
                    elseif param == DistUInt32
                         sum(
                            @dice_ite if flip_for(rs, "$(zero_prefix)$(ty)_$(ctor)_$(i)_num$(n)", dependents)
                                DistUInt32(n)
                            else
                                DistUInt32(0)
                            end
                            for n in twopowers(p.intwidth)
                        )
                    else
                        error()
                    end
                    for (i, param) in enumerate(params)
                ]...)
                for (ctor, params) in variants(ty)
                if size != 0 || all(param != ty for param in params) 
            ])
        end
    end
    type_to_gen[p.root_ty](p.ty_sizes[p.root_ty], empty_stack(p))
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
        case = "(" * join([tocoq(eval(Meta.parse(x))) for x in split(case, "%")], ", ") * ")"
        val = thousandths(val)
        push!(get!(matchid_to_cases, matchid, []), (case, val))
    end

    tys, type_ctor_to_id = collect_types(p.root_ty)

    workload = workload_of(typeof(p))
    generators = []

    stack_vars = ["(stack$(i) : nat)" for i in 1:p.stack_size]
    function mk_match(matchid)
        cases = matchid_to_cases[matchid]
        cases = sort(cases)
        "match (size, ($(join(stack_vars, ", ")))) with 
$(join([" " ^ 9 * "| $(name) => $(w)" for (name, w) in cases], "\n"))
         | _ => 500
         end"
    end

    update_stack_vars(loc) = join(stack_vars[2:end], " ") * " $(loc)"
    variants2(ty, zero_case) = if zero_case
        [
            (ctor, params)
            for (ctor, params) in variants(ty)
            if all(param != ty for param in params) 
        ]
    else
        variants(ty)
    end


    for ty in tys
        push!(generators, "
Fixpoint gen_$(to_coq(ty)) (size : nat) $(join(stack_vars, " ")) : G $(to_coq(ty)) :=
  match size with
$(join([
"  | $(if zero_case 0 else "S size'" end) => 
    $(if length(variants2(ty, zero_case)) > 1 "freq [" else "" end)
    $(join([
"    (* $(ctor) *)

    $(if length(variants2(ty, zero_case)) > 1
        "(
         $(mk_match("$(if zero_case "0_" else "" end)$(ty)_variant_$(ctor)")),
         " else "" end)
            $(sandwichjoin(
                Iterators.flatten([
                if param == ty
                    ["bindGen (gen_$(to_coq(param)) size' $(
                        update_stack_vars(type_ctor_to_id[(ty, ctor)])
                    )) (fun p$(i) : $(to_coq(param)) =>" => ")"]
                elseif param ∈ tys
                    ["bindGen (gen_$(to_coq(param)) $(p.ty_sizes[param]) $(
                        update_stack_vars(type_ctor_to_id[(ty, ctor)])
                    )) (fun p$(i) : $(to_coq(param)) =>" => ")"]
                elseif param == AnyBool
                    ["let weight_true := $(mk_match("$(if zero_case "0_" else "" end)$(ty)_$(ctor)_$(i)")) in
                    bindGen (freq [
                        (weight_true, true);
                        (1000-weight_true, false)
                    ]) (fun p$(i) : $(to_coq(param)) =>" => ")"]
                elseif param == DistUInt32
                    [
                        "let weight_$(n) := $(mk_match("$(if zero_case "0_" else "" end)$(ty)_$(ctor)_$(i)_num$(n)")) in
                        bindGen (freq [
                            (weight_$(n), returnGen $(n));
                            (1000-weight_$(n), returnGen 0)
                        ])
                        (fun n$(n) : nat => $(if j == p.intwidth "
                        let p$(i) := $(join(["n$(n)" for n in twopowers(p.intwidth)], "+ ")) in " else "" end)
                        " => ")"
                        for (j, n) in enumerate(twopowers(p.intwidth))
                    ]
                else
                    error()
                end
                for (i, param) in enumerate(params)
                ]),
            middle="returnGen ($(ctor) $(join(["p$(i)" for i in 1:length(params)], " ")))",
            sep="\n"))
    $(if length(variants2(ty, zero_case)) > 1 ")" else "" end)
        "
        for (ctor, params) in variants2(ty, zero_case)
    ], ";\n"))
    $(if length(variants2(ty, zero_case)) > 1 "]" else "" end)"
    for zero_case in [true, false]
  ], "\n" ))
    end.")
    end

    before, after = sandwich(workload)
    "$(before)
    $(join(generators, "\n"))

Definition gSized :=
  gen_$(to_coq(p.root_ty)) $(p.ty_sizes[p.root_ty])$(" 0" ^ p.stack_size).

    $(after)"
end