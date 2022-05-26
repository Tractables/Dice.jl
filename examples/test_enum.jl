using Dice

@enum Colors red green blue
code = @dice begin
    if flip(1/10)
        DistEnum(red)
    elseif flip(2/9)
        DistEnum(green)
    else
        DistEnum(blue)
    end
end
bdd = compile(code)
dist = infer(bdd)
@assert sum(values(dist)) ≈ 1
@assert dist[red] ≈ 1/10
@assert dist[green] ≈ 2/10
@assert dist[blue] ≈ 7/10

code = @dice begin
    x = if flip(1/10)
        DistEnum(red)
    elseif flip(2/9)
        DistEnum(green)
    else
        DistEnum(blue)
    end
    y = if flip(1/10)
        DistEnum(red)
    elseif flip(2/9)
        DistEnum(green)
    else
        DistEnum(blue)
    end
    prob_equals(x, y)
end
bdd = compile(code)
@assert infer(bdd) ≈ (1/10)^2 + (2/10)^2 + (7/10)^2
