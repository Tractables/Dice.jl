import numpy as np
import matplotlib.pyplot as plt
from matplotlib.pyplot import figure

def data_extract(name):
    handle = open("/space/poorvagarg/" + name + ".csv", "r")
    lines = handle.readlines()
    lines = lines[2:]

    x = []
    c = []
    d = []
    e = []
    for i in range(6):
        current = lines[i].split(",")
        print(current)
        x.append(int(current[0]))
        c.append(float(current[2]))
        d.append(float(current[3]))
        e.append(float(current[4]))

    for i in [6]:
        current = lines[i].split(",")
        print(i)
        print(current[0], current[2], current[4])
        x.append(int(current[0]))
        c.append(float(current[2]))
        e.append(float(current[4]))

    for i in range(7, 10):
        current = lines[i].split(",")
        x.append(int(current[0]))
        e.append(float(current[4]))

    return (x, c, d, e)

categs = ["less", "equals", "sum"]


l = ["a < b", "a == b", "a + b"]

a = data_extract("sum")

fig = plt.figure(figsize=(24,4))


for num in range(1, 4):
    print(num)
    (x, imp_klds, col_klds, gibbs_klds) = data_extract(categs[num-1])
    ax = fig.add_subplot(1,3,num)
    ax.plot(range(len(imp_klds)),imp_klds,label="hybrid",linewidth=4, linestyle='dashed')
    ax.plot(range(len(col_klds)),col_klds,label="native",linewidth=4, linestyle='dotted')
    ax.plot(range(len(gibbs_klds)),gibbs_klds,label="binary",linewidth=4)
    ax.set_xlabel("Bits",fontsize=24)
    ax.set_yscale('log')
    ax.set_title(l[num-1], fontsize=24, y = 0.93, pad = -14)
    # ax.set_figwidth(2)
    # ax.set_figheight(2)
    if(num==1):
        ax.set_ylabel("Time(s)",fontsize=24)
    # ax.set_yticks([-1,-5,-10])
    ax.tick_params(axis='both', which='major', labelsize=24)
    if(num==2):
        ax.legend(loc='upper center', bbox_to_anchor=(0.5, 1.28), ncol=3, fontsize=24)    
    plt.subplots_adjust(wspace=0.3)
	
fig.savefig('problog.png',bbox_inches='tight',dpi=200)


#final final plots
# labels = ['a','b','c']
# szs = ['1','4','8']

# for num in range(1,4):
# 	if(num==1):
# 		res=[]
# 	elif(num==2):
# 		res=[]
# 	elif(num==3):
# 		res=[]

# 	imp_klds=None
# 	col_klds=None
# 	gibbs_klds=None

# 	num_seeds=len(res)//3

# 	wts=None

# 	for a in res:
# 	    if a[1]=="imp":
# 	        if imp_klds is None:
# 	            imp_klds=a[2]
# 	            wts=a[3]
# 	        else:
# 	            for i in range(len(imp_klds)):
# 	                imp_klds[i]+=a[2][i]
# 	    if a[1]=="col":
# 	        if col_klds is None:
# 	            col_klds=a[2]
# 	        else:
# 	            for i in range(len(col_klds)):
# 	                col_klds[i]+=a[2][i]
# 	    if a[1]=="gibbs":
# 	        if gibbs_klds is None:
# 	            gibbs_klds=a[2]
# 	        else:
# 	            for i in range(len(gibbs_klds)):
# 	                gibbs_klds[i]+=a[2][i]

	