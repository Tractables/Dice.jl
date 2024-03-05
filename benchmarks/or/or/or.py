import sys

n = int(sys.argv[1])

lines = ["data real d1;\n", "data real d2;\n"]
lines2 = ["        d1 ~ normal(135, 8);\n", "        d2 ~ normal(135, 8);\n", "} else {\n", "        d1 ~ normal(80, 8);\n", "        d2 ~ normal(80, 8);\n", "}\n"]

f = open(f"or_{n}.txt", "a")
#f.writelines("real prior ~ beta(1, 1);\n")
#f.writelines("int<2> z1 ~ bernoulli(prior);\n")

for i in range(1,n+1):
    f.writelines(f"real prior{i} ~ beta(1, 1);\n")
    f.writelines(f"int<2> z{i} ~ bernoulli(prior{i});\n")

f.writelines(lines)

temp = "z1"
for i in range(2, n+1):
    temp = temp + f" + z{i}"

f.writelines(f"if ((({temp}) - {n}) > 0) " + "{\n")
f.writelines(lines2)

f.close()
