using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin
    # triangle distribution

    function triangle(b::Int)
        s = false
        n = 2^b
        x = Vector(undef, b)
        y = Vector(undef, b)
        for i = b:-1:1
            x[i] = if s flip(1/2) else flip((3n - 2)/ (4n-4)) end
            y[i] = flip((n-2)/(3n-2))
            s = s || (x[i] && !y[i])
            n = n/2
        end
        return ProbInt(x)
    end

    function uniform(b::Int) # b is the bits for uniform, w is the bitwidth
        x = Vector(undef, b)
        for i = b:-1:1
            x[i] = flip(0.5)
        end
        return ProbInt(x)
    end

    function discrete(p::Vector{Float})
        mb = length(p)
        ans = ProbInt
        for i=1:mb
            
    end
    uniform(2)
    # flip(0)
end

@macroexpand @dice begin
    # triangle distribution
    flip(0)

end
bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)