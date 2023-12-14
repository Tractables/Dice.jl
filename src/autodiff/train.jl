export step_maximize!, add_pr_var!

function step_maximize!(var_vals::Valuation, nodes_to_max, learning_rate)
    root_derivs = Derivs(n => 1 for n in nodes_to_max)
    for (n, d) in differentiate(var_vals, root_derivs)
        n isa Var && (var_vals[n] += d * learning_rate)
    end
end

function add_pr_var!(var_vals::Valuation, name_and_pr)
    name, pr = name_and_pr
    @assert 0 < pr < 1
    var = Var("$(name)_before_sigmoid")
    val = inverse_sigmoid(pr)
    @assert !has_key(var_vals, var) || var_vals[var] == val
    var_vals[var] = val
    sigmoid(var)
end

function train_vars!(
    var_vals::Valuation,
    x::ADNode,
    epochs::Integer,
    learning_rate::AbstractFloat,
)
    for _ in 1:epochs
        step_maximize!(var_vals, [x], learning_rate)
    end
end