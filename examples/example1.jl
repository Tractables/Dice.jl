using Alea
code = @dice begin
    a = flip(0.4)
    b = flip(0.6)
    observe(a | b)
    a
end
@show pr(code)