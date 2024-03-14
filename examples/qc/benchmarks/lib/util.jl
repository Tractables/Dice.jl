function backtrack_for(rs, name, opts::Vector{DistI{Opt{T}}})::DistI{Opt{T}} where T
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

function frequency(xs)
    sample_from(xs)
end

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
function map(::Type{RetT}) where RetT
    function inner(f, l::DistI{List{T}}) where T
        match(l, [
            "Nil" => () -> DistNil(RetT),
            "Cons" => (x, xs) -> DistCons(f(x), map(RetT)(f, xs))
        ])
    end
end

function frequency_for(rs, name, xs)
    weights = [register_weight!(rs, "$(name)_$(i)") for i in 1:length(xs)]
    res = last(xs)
    weight_sum = last(weights)
    for i in length(xs) - 1 : -1 : 1
        weight_sum += weights[i]
        res = @dice_ite if flip(weights[i] / weight_sum)
            xs[i]
        else
            res
        end
    end
    res
end

function opt_stlc_str(ast)
    name, children = ast
    if name == "None"
        "None"
    elseif name == "Some"
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

function save_samples(filename, e; n_samples=200, io=stdout)
    open(filename, "w") do file
        for _ in 1:n_samples
            expr = sample(e)
            println(file, opt_stlc_str(expr))
            typecheck_opt(expr)
        end
    end
    println(io, "Saved samples to $(filename).")
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

thousandths(n) = Integer(round(n, digits=3) * 1000)

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
