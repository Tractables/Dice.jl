using Revise
using Alea
using Alea: num_flips, num_nodes, to_dice_ir

code = @dice_ite begin
    function uniform(b::Int, w::Int) # uniform [0, b)
        num_b = 1 * (b == 1) + (ndigits(b, base = 2) - 1) * (b != 1)
        x = Vector(undef, num_b)   
        for i = num_b:-1:1
            x[i] = if b != 1 flip(0.5) else flip(0) end
        end

        ans = DistInt(x)
        return add_bits(ans, w)
    end

    function uniform2(i::Int)
        num_b = ndigits(i, base = 2)
        bits = Vector{Bool}(undef, num_b)
        for bit_idx = 1:num_b
            b::Bool = i & 1
            @inbounds bits[bit_idx] = b 
            i = i >> 1
        end
        sum = 0
        sum_v = Vector(undef, num_b)
        pos = 1
        println(bits)
        for i = 1:num_b
            println(bits[i])
            sum+=2^(i-1) * bits[i]
            sum_v[pos] = sum
            pos += 1
        end 
        println(sum_v)
        ans = (DistInt([flip(0)]))
        println(num_b)
        for i = 2:num_b
            println(i)
            ans = if flip((2^(i-1) * bits[i])/sum_v[i]) 
                (uniform(2^(i-1), 3) + (sum_v[i] - 2^(i-1)*bits[i]))[1] else (ans) end
        end
        return ans
    end
    uniform2(63)
end

# BDD analysis
bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)

# IR analysis
# to_dice_ir(code)
# has_dice_binary() && rundice(code)
# has_dice_binary() && infer(code, :ocaml)