import numpy as np
import math
import sys
import statistics
import csv
import matplotlib.pyplot as plt

gt = 0.5

def stan_accuracy(T, var_name, gt, benchmark_name):
    file_handle = open(f"baselines/stan/or/results_{T}.txt", "r")
    lines = file_handle.readlines()

    answer = 0
    for i in lines:
        current = i.split()
        if current != []:
            if current[0] == var_name:
                answer = float(current[1])

    handle2 = open("../stan_results.txt", "a")
    handle2.writelines(benchmark_name + "," + var_name + "," + str(abs(gt - answer)) + "\n")
    handle2.close()
    print(answer)
    return abs(gt - answer)

def Dice_accuracy(T, result_file, gt, position, flag):
    file_handle = open(f"benchmarks/or/results_{T}.txt", "r")
    lines = file_handle.readlines()
    
    min_error = 100000000
    min_line = ""
    for i in lines:
        bits = float(i.split(",")[0])
        pieces = (math.log2(float((i.split(",")[1]))))
        if pieces < bits/2.0:
            continue
        btime = float(i.split(",")[-1])
        if btime > 1200:
            continue
        cur = float(i.split(",")[position])
        if (flag == None):
            if abs(gt - cur) <= min_error:
                min_error = abs(gt - cur)
                min_line=i
        elif (float(i.split(",")[flag[1]]) == flag[0]):
            if abs(gt - cur) <= min_error:
                min_error = abs(gt - cur)
                min_line = i
        else:
            continue
    return min_error

def WebPPL_accuracy(T, method, gt):
    min_error = 1000000000
    a = 0
    ans = []
    if method == "MCMC":
        if T >= 25:
            number = 23
        else:
            number = 24
    else:
        number = 16
    filename = f"baselines/webppl/or_{T}"+"/output_"+method+"_"+str(number)+".txt"
    file_handle = open(filename, "r")

    lines = file_handle.readlines()
    for i in lines:
        if i.split() == []:
            continue
        if i.split()[0] == "{":
            if int(i.split()[-2]) > 1200000:
                continue
            ans.append(abs(float(i.split()[2][:-1]) - gt))
        else:
            continue
    
    cur = statistics.mean(ans)
    if (cur < min_error):
        a = number
        min_error = cur
    return min_error

# Collecting Stan numbers
stan_files = [5, 10, 15]
stan_res = []

for i in stan_files:
    stan_res.append(stan_accuracy(i, "prior1", gt, f"or_{i}"))

print(stan_res)

# Collecting HyBit numbers
dice_files2 = [i for i in range(5, 55, 5)]

dice_res = []
for i in dice_files2:
    dice_res.append(Dice_accuracy(i, f"results_{i}.txt", 0.5, 2, None))

dice_res

# Collecting WebPPL numbers
webppl_files2 = [i for i in range(5, 55, 5)]
mcmc_res = []
for i in webppl_files2:
    mcmc_res.append(WebPPL_accuracy(i, "MCMC", gt))

smc_res = []
for i in webppl_files2:
    smc_res.append(WebPPL_accuracy(i, "SMC", gt))

print(mcmc_res, smc_res)

# gubpi numbers

fig, ax = plt.subplots()

plt.rcParams.update({'font.size': 15})
plt.rc('xtick', labelsize=15)
plt.rc('ytick', labelsize=15)
plt.rc('axes', labelsize=20)
plt.xlabel('xlabel', fontsize=18)
plt.ylabel('xlabel', fontsize=18)
plt.rc('legend', fontsize=15)

ax.set_xlabel("Number of Discrete Variables (T)")
ax.set_ylabel("Absolute Error")
ax.plot(stan_files, stan_res, marker = "o", color="orange", linestyle="dashdot")
ax.plot([15], [stan_res[-1]], marker="X", markersize=20, color="orange")
ax.plot(dice_files2, dice_res, marker = "o", color="blue")
ax.plot([5, 10], [0, 0], marker = "o", color="green")

ax.plot([10], [0], marker="X", markersize=20, color="green")
ax.plot(webppl_files2, mcmc_res, marker="o", linestyle="dashed", color="pink")
ax.plot(webppl_files2, smc_res, marker="o", linestyle="dotted", color="red")
# plt.ylim(-0.0004, 0.01)

ax.legend(["Stan", "Stan Timeout", "HyBit", "Psi", "Psi Timeout", "WebPPL MH", "WebPPL SMC"], loc='upper right')
fig.savefig("scripts/figure2/or_error.png", bbox_inches="tight")

