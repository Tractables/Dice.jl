using Combinatorics: permutations

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

# give a weight to the permutation
function weight_of(weights_xs)
    function helper(weights_xs)
        weight, x = weights_xs[1]
        if length(weights_xs) == 1
            Dice.Constant(1), weight
        else
            rest = @view weights_xs[2:end]
            w, rolling_sum = helper(rest)

            rolling_sum += weight
            w *= weight / rolling_sum

            w, rolling_sum
        end
    end
    w, _ = helper(weights_xs)
    w
end

function shuffle(weights_xs)
    weights, xs = [], []
    for (weight, x) in weights_xs
        push!(weights, weight)
        push!(xs,x)
    end

    frequency(
        (weight_of(perm), [x for (weight, x) in perm])
        for perm in permutations(weights_xs)
    )
end

function backtrack(default, weights_xs)
    first_some(default, shuffle(weights_xs))
end

function first_some(default, xs)
    isempty(xs) && return default
    x, rest = xs[1], @view xs[2:end]
    @dice_ite if Dice.matches(x, :Some)
        x
    else
        first_some(default, rest)
    end
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

function freq_flips(weights)
    weight_sum = last(weights)
    flips = Vector(undef, length(weights))
    for i in length(weights) - 1 : -1 : 1
        weight_sum += weights[i]
        flips[i] = flip(weights[i] / weight_sum)
    end
    flips
end

function freq_flips_sample(a, weights)
    weight_sum = compute(a, last(weights))
    flips = Vector(undef, length(weights))
    for i in length(weights) - 1 : -1 : 1
        w = compute(a, weights[i])
        weight_sum += w
        flips[i] = rand() < (w / weight_sum)
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

function freq_choose_sample(xs, flips)
    res = last(xs)
    for i in length(xs) - 1 : -1 : 1
        res = if flips[i]
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

function frequency_sample(a, weights_xs)
    weights, xs = [], []
    for (weight, x) in weights_xs
        push!(weights, weight)
        push!(xs,x)
    end
    freq_choose(xs, freq_flips_sample(a, weights))
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
    key_range(d) = minimum(keys(d)):maximum(keys(d))
    open(filename, "w") do file
        println(file, "val\tprobability")
        for i in key_range(dist)
            println(file, "$(i)\t$(dist[i])")
        end
    end
    println(io, "Saved metric dist to $(filename).")
end

function save_samples(rs, filename, e; n_samples=200)
    open(filename, "w") do file
        a = ADComputer(rs.var_vals)
        for _ in 1:n_samples
            expr_dist = sample_as_dist(rs.rng, a, e)
            expr = Dice.frombits(expr_dist, Dict())
            # diff_test_typecheck(expr_dist, expr)
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

function register_weight!(rs, s; random_value=false)
    var = Var("$(s)_before_sigmoid")
    if !haskey(rs.var_vals, var) || rs.var_vals[var] == 0
        rs.var_vals[var] = 0
        rs.coupled_ad_computer.vals[var] = 0
    # else
    #     println("WARNING: not registering fresh weight for $(s)")
    end
    if random_value
        v = inverse_sigmoid(rand(rs.rng))
        rs.var_vals[var] = v
        rs.coupled_ad_computer.vals[var] = v
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
        # t = join([string(x) for x in dependents_vals], "%")
        t = join([string(Dice.frombits(x,Dict())) for x in dependents_vals], "%")
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

function flip_for_sample(rs, a, name, dependents)
    t = join([string(x) for x in dependents], "%")
    # t = join([string(Dice.frombits(x,Dict())) for x in dependents_vals], "%")
    rand() < compute(a, register_weight!(rs, "$(name)%%$(t)"))
end

function backtrack_for(rs, name, dependents, casenames_xs, default)
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
        t = join([string(Dice.frombits(x,Dict())) for x in dependents_vals], "%")
        weights = [
            register_weight!(rs, "$(name)_$(casename)%%$(t)")
            for casename in casenames
        ]
        v = backtrack(default, collect(zip(weights, xs)))
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
        t = join([string(Dice.frombits(x,Dict())) for x in dependents_vals], "%")
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

function frequency_for_sample(rs, a, name, dependents, casenames_xs)
    casenames = []
    xs = []
    for (casename, x) in casenames_xs
        push!(casenames, casename)
        push!(xs, x)
    end

    res = nothing
    # support = support_mixed(dependents; as_dist=true)
    # @assert !isempty(support)
    t = join([string(x) for x in dependents], "%")
    # t = join([string(Dice.frombits(x,Dict())) for x in dependents_vals], "%")
    weights = [
        register_weight!(rs, "$(name)_$(casename)%%$(t)")
        for casename in casenames
    ]
    res = frequency_sample(a, collect(zip(weights, xs)))
    @assert Dice.isdeterministic(res)
    res
end


function value_to_coq(i::Integer)
    "$(i)"
end

function value_to_coq(i::DistUInt32)
    Dice.frombits(i, Dict())
end

function value_to_coq(v::Tuple)
    if v == ()
        "tt"
    else
        "($(join([value_to_coq(x) for x in v], ", ")))"
    end
end


# freq [
#     Var1, e1
#     Var2, e2
# ]
# freq [
#     Var1, e1
#     Var3, e1
# ]


# currently:
# initialize a from rs.var_vals
# register Var1 to rs.var_vals
# register Var2 to rs.var_vals
# compute Var1 using a
# compute Var2 using a
# register Var3 to rs.var_vals
# compute Var1 using a
# compute Var2 using a


# register Var1 to rs.var_vals
# register Var2 to rs.var_vals
# register Var3 to rs.var_vals
# initialize a from rs.var_vals
# compute Var1 using a
# compute Var2 using a
# compute Var1 using a
# compute Var2 using a
