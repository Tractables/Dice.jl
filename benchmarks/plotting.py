import matplotlib.pyplot as plt
import math
from scipy.special import rel_entr

a = open("/home/poorvagarg/.julia/dev/Dice/pi_results.txt", "r")
pi_julia_acc = a.readlines()
pi_julia_acc = pi_julia_acc[0:15]

# pi_julia_accuracy = readdlm("/home/poorvagarg/.julia/dev/Dice/pi_results.txt", ',', Float64, '\n')
pi_julia_bdd = [5, 10, 22, 51
, 119
, 269
,602
,1315
,2841
,6079
,12953
,27380
,57712
,121147
,253939
,530499
,1107219
,2304443]


t = [i for i in range(1, 16)]
pi_kld = [math.log(float(j.split(',')[2])) for j in pi_julia_acc]
pi_time = [float(j.split(',')[3]) for j in pi_julia_acc]
tic = [(t[i], pi_julia_bdd[i]) for i in range(0, 15)]

fig1, ax1 = plt.subplots()

ax1.plot(pi_kld, pi_time, color= "green")
ax1.set_xlabel('Log(KL)')
ax1.set_ylabel('Time(in ms)')
ax1.set_title("Pi")
for i in range(len(tic)):
    ax1.annotate(tic[i], (pi_kld[i], pi_time[i]))

a = open("/home/poorvagarg/.julia/dev/Dice/pi_sample.txt", "r")
pi_acc = a.readlines()
# pi_acc = pi_acc[:-1]

t = [str(10) + "^" + str(i) for i in range(1, 8)]
prob = (5 - math.pi)/4
pi_kld = [math.log(sum(rel_entr([prob, 1 - prob], [float(j.split(' ')[1]), 1 - float(j.split(' ')[1])]))) for j in pi_acc]
pi_time = [float(j.split(' ')[0]) for j in pi_acc]
print(pi_kld)
# tic = [(t[i], pi_julia_bdd[i]) for i in range(0, 18)]

ax1.plot(pi_kld, pi_time, color= "blue")
ax1.legend(["BitBlast:(bits, BDD size)", "Sampling"])

for i in range(len(t)):
    ax1.annotate(t[i], (pi_kld[i], pi_time[i]))
fig1.savefig("pi.png")