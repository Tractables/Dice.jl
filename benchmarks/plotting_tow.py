import matplotlib.pyplot as plt
import math
from scipy.special import rel_entr

a = open("/home/poorvagarg/.julia/dev/Dice/tow_acc.txt", "r")
b = open("/home/poorvagarg/.julia/dev/Dice/tow_bdd.txt", "r")
acc = a.readlines()
bdd = b.readlines()

x = [math.log(sum(rel_entr([0.5, 0.5], [float(j.split(',')[2]), 1 - float(j.split(',')[2])]))) for j in acc]
y = [float(j.split(',')[3]) for j in acc]

tic = [(j.split(',')[0], j.split(',')[1], j.split(',')[3][:-1]) for j in bdd]

fig1, ax1 = plt.subplots()

# ax1.plot(x, y, color= "green")
ax1.set_xlabel('Log(KL)')
ax1.set_ylabel('Time(in ms)')
ax1.set_title("Tug of War")
# for i in range(len(tic)):
#     ax1.annotate(tic[i], (x[i], y[i]))

c = open("/home/poorvagarg/.julia/dev/Dice/tow_mcmc.txt", "r")
mcmc = c.readlines()
mcmc = mcmc[:5]

x = [math.log(sum(rel_entr([0.5, 0.5], [float(j.split(' ')[1]), 1 - float(j.split(' ')[1])]))) for j in mcmc]
y = [float(j.split(' ')[0]) for j in mcmc]

t = [str(10) + "^" + str(i) for i in range(1, 8)]

ax1.plot(x, y, color= "blue")
for i in range(len(t)):
    ax1.annotate(t[i], (x[i], y[i]))

d = open("/home/poorvagarg/.julia/dev/Dice/tow_rej.txt", "r")
rej = d.readlines()
rej = rej[:5]

x = [math.log(sum(rel_entr([0.5, 0.5], [float(j.split(' ')[1]), 1 - float(j.split(' ')[1])]))) for j in rej]
y = [float(j.split(' ')[0]) for j in rej]

t = [str(10) + "^" + str(i) for i in range(1, 8)]

ax1.plot(x, y, color= "yellow")
for i in range(len(t)):
    ax1.annotate(t[i], (x[i], y[i]))
# ax1.legend(["BitBlast:(bits, log2(pieces), BDD size)", "MCMC", "Rejection"])
fig1.savefig("tow.png")
