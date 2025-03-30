using Alea
using Alea: num_flips, num_nodes, to_dice_ir

#TODO: the code below is not correct
code = @alea_ite begin
    # triangle distribution

    function triangle(b::Int)
        s = false
        m = 2^(2b)
        n = 2^b
        x = Vector(undef, b)
        y = Vector(undef, b)
        for i = b:-1:1
            x[i] = if s flip(1/2) else flip((m/2-n/2)/(m-n)) end
            y[i] = x[i] || flip(1/(3/2-n/m))
            s = s || (!x[i] && y[i])
            m = m/4
            n = n/2
        end
        return DistInt(x)
    end

    for b = 1:16
        t = triangle(b)
        println("$b-bit triangle uses $(num_flips(t)) flips and $(num_nodes(t)) BDD nodes")
    end
    triangle(2)

end
bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)