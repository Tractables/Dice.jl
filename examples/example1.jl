using Dice
code = @dice begin
    a = flip(0.4)
    b = flip(0.6)
    observe(a | b)
    c = if flip(0.5) a else b end
    c
end
@show pr(code)