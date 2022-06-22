using Dice

function finite_quotient(x,y)
    require_dice_transformation()
    if !x && !y
        prob_error("0/0 is undefined")
        false
    elseif x && !y
        false
    else
        true
    end
end

quo, errors, observation = @dice begin
    finite_quotient(flip(0.5), flip(0.5))
end
total_error = reduce(|, [err for (err, msg) in errors])
dist, error_p = infer(quo, err=total_error)
@assert dist[true] ≈ 0.5
@assert error_p ≈ 0.25

function less_than(a, b)
    require_dice_transformation()
    if a & !b
        return DistTrue()
    end
    return DistFalse()
end

d, errors, obs = @dice less_than(flip(0.3), flip(0.5))
@assert infer_bool(d, observation=obs) ≈ 0.15

d, a, obs = @dice begin
    flipA = flip(0.3)
    flipB = flip(0.5)
    observe(flipA)
    less_than(flipA, flipB)
end
@assert infer_bool(d, observation=obs) ≈ 0.5
