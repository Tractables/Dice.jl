using Revise
using Dice

a = flip(0.5; learn = true)
b = ifelse(a, flip(0.3), flip(0.2))
pr(b)

a = flip(0.25)
b = ifelse(a, flip(0.3), flip(0.2))
pr(b)
