using Dice
using Zygote

function f(psp)
    prob = sigmoid(psp)
    x = flip(prob) & flip(prob) & !flip(prob)
    pr(x)
end
gradient(f, 0)

Dice.node_logprob

using ChainRules
ChainRules.rrule(::typeof(Dice))
function rrule(::typeof(Dice.node_logprob), pr, hi, lo)
    Dice.node_logprob
end