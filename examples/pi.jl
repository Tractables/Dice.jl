using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin
            x = (uniform(dicecontext(), 15, DistFixParam{16, 16}) + DistFixParam{16, 16}(dicecontext(), 1))[1]
            y = (uniform(dicecontext(), 15, DistFixParam{16, 16}) + DistFixParam{16, 16}(dicecontext(), 1))[1]
            # x = DistFixParam{3, 0}(dicecontext(), 1)
            # y = DistFixParam{3, 0}(dicecontext(), 4)
            # z = (x.number % y.number)
            # z1 = z[1]

            # t = if (z1 > DistInt(dicecontext(), 2047))
            #         ((x.number / y.number)[1] + 1)[1]
            # else
            #         (x.number / y.number)[1]
            # end
            t = round_division(x.number, y.number)
            # t
            # Cond(!t.bits[1], !prob_equals(y.number, 0))
            !t.bits[1]
            # Cond(z[1], !z[2])
            # (x.number / y.number)[1]
end

# a = compile(code)
b = infer(code, :bdd)
pi - (5 - 4*(b))
prob = 0
for i=1:2:length(b)
    prob += b[i][2]
end
num_flips(a)
num_nodes(a)