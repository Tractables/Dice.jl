import sys
import string

f = open(sys.argv[1], "r+")
a = f.readlines()

trDa = 0
trPr = 0
para = 0
model = 0
limit = len(a)
for l in range(limit):
    i = a[l]
    # print(i.split("{"))
    if i.split("{")[0] == "transformed data ":
        trDa = l
    if i.split("{")[0] == "transformed parameters ":
        trPr = l
    if i.split("{")[0] == "parameters ":
        para = l
    if i.split("{")[0] == "model ":
        model = l
#print(trDa, trPr, para, model)
temp = a[0:trDa] + a[para:trPr] + a[trPr:model-1] + a[trDa+1:para-1] + a[model-2:] 
a = temp

var_dict = {}
for_vars = []

for l in range(len(a)):
    i = a[l]
    t1 = i.split()
    if len(t1) > 0:
        if "real[" in t1[0]:
            var_name = t1[1][:-1]
            comma = t1[0].count(",")
 #           print(comma)
            var_length = 2**(comma+1)
            t2 = "\t" + f"real {var_name}[{var_length}];" + "\n"
            a[l] = t2
            var_dict[var_name] = var_length
    if "rep_vector" in i:
        if i.split()[0][0] != 'a':
            comma = i.count(",")
            eq = i.find("=")
            t2 = i[:eq+1] + f" rep_array(0, {2**comma});" + "\n"
            a[l] = t2

    if "for(" in i:
        for_vars.append(i.split()[0][4:])

    if "[[" in i:
        t1 = i.split()
        for_vars = for_vars[:-1]
        comma = len(for_vars) - 1
        t2 = f"({for_vars[-1]} - 1)*{2**comma}"
        comma -= 1
        for_vars.reverse()
        for k in for_vars[1:]:
            t2 = t2 + f"+({k}-1)*{2**comma}"
            comma -=1
        t3 = i[:i.find("[[")] + "[" + t2 + "+1"+i[i.find("]]") + 1:]
        a[l] = t3
        for_vars = []

    if "+= m" in i:
        if not ("target" in i):
            comma = i.count(",")
            t1 = i.split("[")
  #          print(t1[-1].split("]"))
            t2 = t1[-1].split("]")[0].split(",")
            t3 = f"({t2[0]} - 1)*{2**comma}"
            comma -= 1
            # t2.reverse()
            for k in t2[1:]:
                t3 = t3 + f"+({k}-1)*{2**comma}"
                comma -=1

            t4 = t1[0] + "[" + t1[1] + "[" + t3 + "+1];\n"
            a[l] = t4

    # for l in range(len(a)):
    #     i = a[l]
    if "real prior" in i:
        a[l] = i.replace("real prior", "real<lower=0, upper=1> prior")
    # if "real[" in i:
    #     j = i.replace("real", "vector")
    #     a[l] = j
    if "bernoulli_lpmf" in i:
        pt = i.find("|")
        a[l] = i[:pt] + " - 1 " + i[pt:]






"""
for l in range(len(a)):
    i = a[l]
    if "real[" in i:
        t1 = i.split("[")
        t2 = t1[1].split("]")

        new_string = t1[0] + t2[1][:-2] + "[" + t2[0] + "];\n"
        #print(new_string)
        a[l] = new_string


"""
f.close()

f = open(sys.argv[1], "w")
for i in a:
    f.writelines(i)

f.close()
