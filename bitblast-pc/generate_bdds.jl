using Dice

a = flip(0.5)
b = flip(0.5)

and = a & b
dump_dot(and, filename="bitblast-pc/and.dot")

or = a | b
dump_dot(or, filename="bitblast-pc/or.dot")

c = ifelse(a, b, !b)
dump_dot(c, filename="bitblast-pc/if.dot")