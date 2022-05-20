using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin
    function discrete2(p::Vector{Float64}, t::Type)

        function recurse(p::Vector, i, s, e, prob::Vector)
            if (i == 0)
                flip(sum(prob[Int((s+e+1)/2):e])/sum(prob[s:e]))
            else
                (if p[length(p) - i + 1] recurse(p, i-1, Int((s+e+1)/2), e, prob) else recurse(p, i-1, s, Int((s+e-1)/2), prob) end)
            end
        end

        mb = length(p)
        add = Int(ceil(log2(mb)))
        p_proxy = vcat(p, zeros(2^add - mb))
        int_vector = []
        
        for i=1:add
            @show i
            a = recurse(int_vector, i-1, 1, 2^add, p_proxy)
            push!(int_vector, a)
        end
        t(reverse(int_vector))
    end

    size = 10
    a = Vector{Float64}(undef, 2^size)
    for i = 1:2^size
        a[i] = 1/2^size
    end
    b = discrete2(a, DistInt)
    prob_equals(b, 0)
end

# BDD analysis
bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)