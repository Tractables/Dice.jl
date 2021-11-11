using Pkg; Pkg.activate(@__DIR__);

using Dice

print(@dice_ir begin
    n = 2
    x = Vector(undef, n)
    x[1] = flip(0.5)
    for i=2:n
        x[i] = if x[i-1]
            flip(0.9)
        else
            flip(0.5)
        end
    end
    x[end]
end)

@dice_run begin
    n = 2
    x = Vector(undef, n)
    x[1] = flip(0.5)
    for i=2:n
        x[i] = if x[i-1]
            flip(0.9)
        else
            flip(0.5)
        end
    end
    x[end]
end
