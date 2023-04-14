import numpy as np
import matplotlib.pyplot as plt
from matplotlib.pyplot import figure

x = [2, 3, 4, 5, 6, 7, 8]
webppl = [0.0048, 0.0228, 0.1288, 0.6068, 5.241, 59.4592, 622.5, 5582.102]
dp = [0.0762, 1.0858, 16.904, 225.823]
psi = [0.4122, 56.632, 7966.656]
dice = [0.0119, 0.0106, 0.0161, 0.018, 0.0212, 0.0291, 0.0372, 0.0528]

fig = plt.figure(figsize=(6,3))
# ls = ["webppl", "dp", "psi", "dice"]
# for i in [webppl, dp, psi, dice]:
#     fig.plot(x[0:len(i)], i, label=ls[])


for num in range(1, 2):
    print(num)
    (x, imp_klds, col_klds, gibbs_klds, dice) = (x, webppl, dp, psi, dice)
    ax = fig.add_subplot(1,1,num)
    ax.plot(range(len(imp_klds)),imp_klds,label="WebPPL",linewidth=4, linestyle='dashed')
    ax.plot(range(len(col_klds)),col_klds,label="Psi (DP)",linewidth=4, linestyle='dotted')
    ax.plot(range(len(gibbs_klds)),gibbs_klds,label="Psi",linewidth=4, linestyle="dashdot")
    ax.plot(range(len(dice)),dice,label="Dice.jl",linewidth=4)
    ax.set_xlabel("# Digits",fontsize=24)
    ax.set_yscale('log')
    ax.set_title("Runtime for varying ID digits", fontsize=24, y = 1.00, pad = -14)
    # ax.set_figwidth(2)
    # ax.set_figheight(2)
    if(num==1):
        ax.set_ylabel("Runtime(s)",fontsize=24)
    # ax.set_yticks([-1,-5,-10])
    ax.tick_params(axis='both', which='major', labelsize=24)
    if(num==1):
        ax.legend(loc='upper center', bbox_to_anchor=(0.5, 1.78), ncol=2, fontsize=24)    
    plt.subplots_adjust(wspace=0.3)
	
fig.savefig('luhn.png',bbox_inches='tight',dpi=200)

def data_extract(name):
    handle = open("/space/poorvagarg/" + name + ".csv", "r")
    lines = handle.readlines()
    lines = lines[2:]

    x = []
    c = []
    d = []
    e = []
    for i in range(13):
        current = lines[i].split(",")
        if current[0] == "":
            break
        x.append(int(current[0]))

    for i in range(13):
        current = lines[i].split(",")
        if current[6] == "":
            break
        c.append(float(current[6]))
    
    for i in range(13):
        current = lines[i].split(",")
        if current[7] == "":
            break
        d.append(float(current[7]))

    for i in range(13):
        current = lines[i].split(",")
        if current[10] == "":
            break
        e.append(float(current[10]))

    return (x, c, d, e)

categs = ["less", "equals", "sum"]


l = ["a < b", "a == b", "a + b"]

a = data_extract("sum")

fig = plt.figure(figsize=(24,4))


for num in range(1, 4):
    print(num)
    (x, imp_klds, col_klds, gibbs_klds) = data_extract(categs[num-1])
    ax = fig.add_subplot(1,3,num)
    ax.plot(range(len(imp_klds)),imp_klds,label="one-hot",linewidth=4, linestyle='dashed')
    ax.plot(range(len(col_klds)),col_klds,label="binary",linewidth=4, linestyle='dotted')
    ax.plot(range(len(gibbs_klds)),gibbs_klds,label="Dice.jl",linewidth=4)
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
	
fig.savefig('dice.png',bbox_inches='tight',dpi=200)


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

	