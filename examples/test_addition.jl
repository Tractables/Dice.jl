using Revise
using Dice

LEN = 4
a = uniform(DistUInt{LEN}, LEN-1)
# b = uniform(DistUInt{LEN}, LEN-1) 
b0 = flip(0.5)
b = DistUInt([b0, b1])
print("-- By Dice Code -- ")
c = a+b 

input_names = string.(get_flips(c) .|> x -> x.global_id)


output_names = ["c[4]", "c[3]", "c[2]", "c[1]", "c[0]"]
dump_dot(c, filename="byDiceCode2.dot", inames=input_names, onames=["c[4]", "c[3]", "c[2]", "c[1]", "c[0]"])
print("\tNUM NODES: ", num_nodes(c))
print("-- END: By Dice Code -- \n")


R = uniform(DistUInt{8}, 7)
G = uniform(DistUInt{8}, 7)
four = DistUInt{8}([false, false, false, false, false, true, false, false])  # Binary 00000100
two  = DistUInt{8}([false, false, false, false, false, false, true, false])  # Binary 00000010
one = DistUInt{8}([false, false, false, false, false, false, false, true])

Z = R + G
input_names_colors = string.(get_flips(Z) .|> x -> x.global_id)
dump_dot(Z, inames=input_names_colors,filename="no-division-coloring.dot")
W = (R / four) + (G / two)
input_names_colors_2 = string.(get_flips(W) .|> x -> x.global_id)
dump_dot(W, inames=input_names_colors_2, filename="just-division-coloring.dot")
print("\tZ = NUM NODES: ", num_nodes(Z))
print("\tW = NUM NODES = ", num_nodes(W))

# --- Basic Unit tests for diff sizes -- 
d = uniform(DistUInt{3}, 2)
e = uniform(DistUInt{3}, 2)
f = d+e
input_names = string.(get_flips(f) .|> x -> x.global_id)
print("\tNUM NODES f (4 random vars) = ", num_nodes(f))
dump_dot(f, inames=input_names, filename="threexthree.dot")

d = uniform(DistUInt{4}, 3)
e = uniform(DistUInt{4}, 3)
f = d+e
input_names = string.(get_flips(f) .|> x -> x.global_id)
print("\tNUM NODES f (6 random vars)= ", num_nodes(f))
dump_dot(f, inames=input_names, filename="fourxfour.dot")

d = uniform(DistUInt{5}, 4)
e = uniform(DistUInt{5}, 4)
f = d+e
input_names = string.(get_flips(f) .|> x -> x.global_id)
print("\tNUM NODES f ( 4x4 with overflow room )= ", num_nodes(f))
dump_dot(f, inames=input_names, filename="fivexfive.dot")

# -- End basic unit tests --


a = uniform(DistUInt{8}, 7)
b = uniform(DistUInt{8}, 7) 
print("-- Complicated Ex -- ")
c = a+b 
dump_dot(c, filename="isthisabdd.dot")
print("\tNUM NODES: ", num_nodes(c))


a = uniform(DistUInt{8}, 7)
b = uniform(DistUInt{8}, 7) 
print("-- By Dice Code -- ")
print(a.bits)
print(b.bits)
c = a+b 
print(a.bits)
print(b.bits)
print(c.bits)
c
dump_dot(c, filename="byDiceCode.dot")
print("\tNUM NODES: ", num_nodes(c))
print("-- END: By Dice Code -- \n")


print("-- Adding Four -- \n")
d = uniform(DistUInt{4}, 3)
e = uniform(DistUInt{4}, 3)
f = uniform(DistUInt{4}, 3)
g = uniform(DistUInt{4}, 3)
h = d+e
i = f+g
j = h+i
dump_dot(j, filename="fourAddition.dot")
print("\tNUM NODES: ", num_nodes(j))
print("-- END: Adding Four -- \n")

b3 = flip(0)
c3 = flip(0)
b1 = flip(0.5)
c1 = flip(0.5)
b2 = flip(0.5)
c2 = flip(0.5)

bb = DistUInt{3}([b3,b1,b2])
cc = DistUInt{3}([c3,c1,c2])
aa = bb+cc
dump_dot(aa, filename="Manual_ordering.dot")


# if using observe, need @dice macro 

# dump_dot 
    # @ dice doesn't return probabilistic data structure
    # but what it does return has fields that are probabilistic data structures