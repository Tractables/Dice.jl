using Revise 
using Dice 

# --- Basic Unit tests for diff sizes -- 
d = uniform(DistUInt{3}, 2)
e = uniform(DistUInt{3}, 2)
f = d-e
input_names = string.(get_flips(f) .|> x -> x.global_id)
print("\tNUM NODES f (4 random vars) = ", num_nodes(f))
dump_dot(f, inames=input_names, filename="threexthree.dot")

d = uniform(DistUInt{4}, 3)
e = uniform(DistUInt{4}, 3)
f = d-e
input_names = string.(get_flips(f) .|> x -> x.global_id)
print("\tNUM NODES f (6 random vars)= ", num_nodes(f))
dump_dot(f, inames=input_names, filename="fourxfour.dot")

d = uniform(DistUInt{5}, 4)
e = uniform(DistUInt{5}, 4)
f = d-e
input_names = string.(get_flips(f) .|> x -> x.global_id)
print("\tNUM NODES f ( 4x4 with overflow room )= ", num_nodes(f))
dump_dot(f, inames=input_names, filename="fivexfive.dot")

d = uniform(DistUInt{8}, 7)
e = uniform(DistUInt{8}, 7)
f = d-e
input_names = string.(get_flips(f) .|> x -> x.global_id)
print("\tNUM NODES f ( 4x4 with overflow room )= ", num_nodes(f))
dump_dot(f, inames=input_names, filename="fivexfive.dot")


# -- End basic unit tests --

# If-then-else complicated
aa = DistUInt([flip(0.0), flip(0.5), flip(0.5), ifelse(flip(0.5), flip(0.4), flip(0.6))])
bb = uniform(DistUInt{4}, 3)
cc=aa-bb
input_names = string.(get_flips(cc) .|> x -> x.global_id)
dump_dot(cc, inames=input_names, filename="ifthenelse-sub.dot")
print("\tNum Nodes if-then-else: ", num_nodes(cc))
