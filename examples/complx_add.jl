using Revise
using Dice


a = DistUInt([flip(0.0), flip(0.5), ifelse(flip(0.5), flip(0.4), flip(0.6))])
b = uniform(DistUInt{3}, 2)
c=a+b
input_names = string.(get_flips(c) .|> x -> x.global_id)
dump_dot(c, inames=input_names, filename="ifthenelse.dot")
print("\tNum Nodes if-then-else: ", num_nodes(c))

# code = @dice begin
#     a = DistUInt([flip(0.0), flip(0.5), if flip(0.5) flip(0.4) else flip(0.6) end])

#     b = uniform(DistUInt{3}, 2)
#     c=a+b
# end

# bdd = code.returnvalue
# input_names = string.(get_flips(bdd) .|> x -> x.global_id)
# dump_dot(bdd, inames=input_names, filename="ifthenelse.dot")
# print("\tNum Nodes if-then-else: ", num_nodes(bdd))

# code2 = @dice begin
#     b = uniform(DistUInt{3}, 2)
#     a = DistUInt([flip(0.0), flip(0.5), if flip(0.5) flip(0.4) else flip(0.6) end])
#     c=a+b
# end

# bdd2 = code2.returnvalue
# input_names = string.(get_flips(bdd2) .|> x -> x.global_id)
# dump_dot(bdd2, inames=input_names, filename="ifthenelse2.dot")
# print("\tNum Nodes if-then-else: ", num_nodes(bdd2))