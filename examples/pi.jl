using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin
            x = (uniform(dicecontext(), 15, DistFixParam{16, 16}) + DistFixParam{16, 16}(dicecontext(), 1))[1]
            y = (uniform(dicecontext(), 15, DistFixParam{16, 16}) + DistFixParam{16, 16}(dicecontext(), 1))[1]

            t = round_division(x.number, y.number)

            !t.bits[1]
            # Cond(z[1], !z[2])
            # (x.number / y.number)[1]
end

a = compile(code)
b = infer(code, :bdd)
num_flips(a)
num_nodes(a)
pi - (5 - 4*(b))
