using Dice
using Distributions
using Revise

# The following code thros error
a = bitblast(DistFix{18, 14}, Normal(0,1), 2^11, -8.0, 8.0)
pr(a)