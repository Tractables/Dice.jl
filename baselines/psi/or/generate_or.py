"""
def main() {
    prior := beta(1, 1);
    z1 := bernoulli(prior);
    z2 := bernoulli(0.5);
    z3 := bernoulli(0.5);
    z4 := bernoulli(0.5);
    z5 := bernoulli(0.5);
    z6 := bernoulli(0.5);
    z7 := bernoulli(0.5);
    z8 := bernoulli(0.5);
    z9 := bernoulli(0.5);
    z10 := bernoulli(0.5);



    y := z1 | z2 | z3 | z4 | z5 | z6 | z7 | z8 | z9 | z10;

    o1 := if y {gauss(1, 1)} else {gauss(-1, 1)};
    o2 := if y {gauss(1, 1)} else {gauss(-1, 1)};
    o3 := if y {gauss(1, 1)} else {gauss(-1, 1)};
    cobserve(o1,1.5);
    cobserve(o2,-1.5);
    //cobserve(o3, -1.5);

    return Expectation(prior);
}
"""

import sys
n = int(sys.argv[1])

print("def main() { ")

for i in range(1,n+1):
    print(f"    prior{i} := beta(1, 1);")
    print(f"    z{i} := bernoulli(prior{i});")
print("    y := ")
for i in range(1,n):
    print(f"z{i} | ")
print(f"z{n};")
print("""
            o1 := if y {gauss(80, 8)} else {gauss(135, 8)};
    o2 := if y {gauss(80, 8)} else {gauss(135, 8)};
    cobserve(o1,79);
    cobserve(o2,136);
    //cobserve(o3, -1.5);

    return Expectation(prior1);
}
""")
