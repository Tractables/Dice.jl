using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin
    # function uniform(b::Int, w::Int) # b is the bits for uniform, w is the bitwidth
    #     x = Vector(undef, b)
    #     for i = b:-1:1
    #         x[i] = flip(0.5)
    #     end
    #     return add_bits(DistInt(x), w - b)
    # end
    sum = uniform(dicecontext(), 4, DistFixParam{10, 0})
    for i = 1:49
        sum = (sum + uniform(dicecontext(), 4, DistFixParam{10, 0}))[1]
    end
    # println(max_bits(sum))
    prob_equals(su)
end

# BDD analysis
@timed bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
a = infer(code, :bdd)
b = a[376]
plot(map(a -> a[1], b), map(a -> a[2], b))
function execute(code)
    @time infer(code, :bdd)
end

execute(code)

# IR analysis
# to_dice_ir(code)
# has_dice_binary() && rundice(code)
# has_dice_binary() && infer(code, :ocaml)