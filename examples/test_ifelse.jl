using Dice
using Dice: ifelse

code = @dice begin
    b = DistInt([DistBool(dicecontext(), false)])
    ifelse(flip(0.5), b, b)
end

bdd = compile(code)
@assert length(bdd.bits) > 0
infer(bdd)
