module BitLatte

function create_line(length, contents)
    line = zeros(Float32, length)
    for (k, v) in contents
        line[k] = v
    end
    line
end

function create_monomial(coefficient, exp_vec, precision=0)
    # TODO: to generaliza the coefficient to be rational 
    denominator = round(Int, 1 * 10^(precision * (sum(exp_vec) + 1)))
    monomial = "["
    # monomial += f"{coefficient.numerator}/{coefficient.denominator},"
    monomial *= "$coefficient/$denominator,"
    str_exp_vec = join([string(Int(exp)) for exp in exp_vec], ",")
    monomial *= "[$str_exp_vec]"
    monomial *= "]"
    monomial
end

function line2str(line, precision)
    scale_line = map((x) -> round(Int, x * 10^precision), line)
    join(scale_line, " ")
end

function Base.parse(::Type{Rational{T}}, x::AbstractString) where {T<:Integer}
    list = split(x, '/'; keepempty=false)
    if length(list) == 1
        return parse(T, list[1]) // 1
    else
        @assert length(list) == 2
        return parse(T, list[1]) // parse(T, list[2])
    end
end

function latte_pr(polytope, true_y, dir="tmp")
    if !isdir(dir)
        mkdir(dir)
    end

    # latte input files
    POLYTOPE_TEMPLATE = "polytope.hrep.latte"
    POLYNOMIAL_TEMPLATE = "polynomial.latte"
    # parameters
    PRECISION = 16

    var_indx = Dict()
    for (i, k) in enumerate(keys(polytope))
        var_indx[k] = i
    end
    
    # WRITE POLYTOPE
    d = length(polytope)  # number of variables
    m = 2 * d + 1  # number of constraints
    # lines = ["$m $(d + 1)"]
    lines = []
    # adding domain
    for (var, domain) in polytope
        lower = create_line(
            d + 1, 
            Dict(var_indx[var] + 1 => 1, 1 => - domain[1])
        )
        push!(lines, lower)  # lower bound
        upper = create_line(
            d + 1, 
            Dict(var_indx[var] + 1 => -1, 1 => domain[2])
        )
        push!(lines, upper)  # upper bound
    end
    # adding query constraints
    content = Dict(1 => true_y["const"])
    for (k, v) in true_y
        if k == "const"
            continue
        end
        content[var_indx[k] + 1] = v
    end
    push!(lines, create_line(d + 1, content))
    
    open("$dir/$POLYTOPE_TEMPLATE", "w") do f
        println(f, "$m $(d + 1)")
        for line in lines
            println(f, line2str(line, PRECISION))
        end
    end

    # WRITE POLYNOMIAL: constant one
    exp_vec = create_line(d, Dict())
    monomials = [(1, exp_vec)]
    monomials = [create_monomial(coefficient, exp_vec) for (coefficient, exp_vec) in monomials]
    polynomial = "[" * join(monomials, ",") * "]"

    open("$dir/$POLYNOMIAL_TEMPLATE", "w") do f
        println(f, polynomial)
    end

    # SOLVE LATTE
    latte_cmd = `integrate --valuation=integrate --cone-decompose --monomials=polynomial.latte polytope.hrep.latte`
    cmd_dir = Cmd(latte_cmd; dir)
    out = read(ignorestatus(cmd_dir), String)
    open(joinpath(dir, "out.txt"),"w") do f
        println(f, out)
    end
    run(Cmd(`rm -f Check_emp.lp Check_emp.lps Check_emp.out numOfLatticePoints`;dir))
    println("done running latte")

    println("start reading results")
    f = open(joinpath(dir, "out.txt"), "r")
    s = read(f, String)
    res = match(r"Answer:.*", s)
    if res !== nothing
        vol = parse(Rational{BigInt}, split(res.match, " ")[2])
        vol = float(vol)
        println(vol)
    else
        println("No results!")
        vol = 0.0
    end
    close(f)

    rm(dir, recursive=true)

    # compute partition function
    Z = 1
    for (_, domain) in polytope
        Z *= abs(domain[2] - domain[1])
    end

    vol / Z
    # Question: how to translate y, Dice.DistAnd into linear constraints true_y?
end

# function calibrate(true_y, boolpr, a, precision)
#     p_t = boolpr[true]

#     # enumerate path
#     b = [([i, i + 1/2^precision], j) for (i, j) in a]

#     function f(path)
#         domain, path_pr = path
#         latte_pr(Dict("x" => domain), true_y) * path_pr
#     end    

#     latte_pr_res = map(f, b)
#     calibration = sum(latte_pr_res)

#     calibration * p_t
# end

function calibrate(true_y, a, precision, dir="tmp")
    # p_t = boolpr[true]

    # enumerate path
    b = [([i, i + 1/2^precision], j) for (i, j) in a]

    function f(path)
        domain, path_pr = path
        latte_pr(Dict("x" => domain), true_y, dir) * path_pr
    end    

    latte_pr_res = map(f, b)
    calibration = sum(latte_pr_res)

    calibration
end 

export calibrate
end

# 0.037161 seconds
# 0.042606 seconds