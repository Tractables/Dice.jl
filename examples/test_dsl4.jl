using Dice

function finite_quotient(x,y)
    if !x && !y
        prob_error("0/0 is undefined")
        false
    elseif x && !y
        false
    else
        true
    end
end


foo(x) = flip(x) ? flip(x/2) : flip(x/4)

@dice begin 
    foo(0.9)
end

quo, errors, observation = @dice begin
    finite_quotient(flip(0.5), flip(0.5))
end
total_error = reduce(|, [err for (err, msg) in errors])
dist, error_p = infer(DWE(quo, total_error))

function less_than(a, b)
    if a & !b
        return DistTrue()
    end
    return DistFalse()
end

infer(@dice begin less_than(flip(0.3), flip(0.5)) end)

d, a, observation = @dice begin
    flipA = flip(0.3)
    flipB = flip(0.5)
    less_than(flipA, flipB)
    # observe(flipA)
    # !prob_equals(flipA, flipB)
end

dist = infer_with_observation(d, observation)