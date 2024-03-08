import math
import matplotlib.pyplot as plt
import numpy as np
from matplotlib import ticker

fig, ax = plt.subplots()
plt.rcParams["figure.figsize"] = [4.5, 4.50]
plt.rcParams.update({'font.size': 15})
plt.rc('xtick', labelsize=15)
plt.rc('ytick', labelsize=15)
plt.rc('axes', labelsize=20)
plt.rc('legend', fontsize=20)
plt.ylim(0, 18)
w = 0.1
scale_y = 100
ticks_y = ticker.FuncFormatter(lambda x, pos: '{0:g}'.format(x/scale_y))
ax.yaxis.set_major_formatter(ticks_y)

file1 = open("benchmarks/multimodal/multimodal/multimodal_samples_1.csv", "r")
lines1 = file1.readlines(100000)
hmc_samples = []
for i in range(-1, -101, -1):
    hmc_samples.append(float(lines1[i].split(",")[-2]))
ax.hist(hmc_samples, bins = np.arange(-6, 6 + w, w), alpha = 0.25, color="red")

file2 = open("benchmarks/multimodal/multimodal/multimodal_samples_2.csv", "r")
lines2 = file2.readlines(100000)
hmc_samples2 = []
for i in range(-1, -101, -1):
    hmc_samples2.append(float(lines2[i].split(",")[-2]))
ax.hist(hmc_samples2, bins = np.arange(-6, 6 + w, w), alpha = 0.25, color="blue")

file = open("benchmarks/multimodal/multimodal_6_256.txt", "r")
hybit_data = file.readlines()
hybit_data = [float(i)*640 for i in hybit_data[0:1024]]
ax.plot([i for i in np.arange(-8, 8, 0.015625)], hybit_data, color="purple")

ax.legend(["HyBit", "Stan HMC Run 1", "Stan HMC Run 2"])
ax.set_xlabel("mu1")

fig.savefig("results/multimodal_hmc.pdf", bbox_inches='tight')

fig, ax = plt.subplots()
plt.rcParams["figure.figsize"] = [4.5, 4.50]
plt.rcParams.update({'font.size': 15})
plt.rc('xtick', labelsize=15)
plt.rc('ytick', labelsize=15)
plt.rc('axes', labelsize=20)
plt.rc('legend', fontsize=20)
plt.ylim(0, 18)
w = 0.1
scale_y = 100
ticks_y = ticker.FuncFormatter(lambda x, pos: '{0:g}'.format(x/scale_y))
ax.yaxis.set_major_formatter(ticks_y)

file1 = open("benchmarks/multimodal/result1MCMC.txt", "r")
lines1 = file1.readlines(100000)
print(lines1[1:-1])
mcmc_samples = []
for i in lines1[1:-1]:
    curr = i.split(", ")
    for j in curr:
        mcmc_samples.append(float(j.strip(" ,\n")))
ax.hist(mcmc_samples, bins = np.arange(-6, 6 + w, w), alpha = 0.25, color="red")

file2 = open("benchmarks/multimodal/result2MCMC.txt", "r")
lines2 = file2.readlines(100000)
mcmc_samples2 = []
for i in lines2[1:-1]:
    curr = i.split(", ")
    for j in curr:
        mcmc_samples2.append(float(j.strip(" ,\n")))
ax.hist(mcmc_samples2, bins = np.arange(-6, 6 + w, w), alpha = 0.25, color="blue")

file = open("benchmarks/multimodal/multimodal_6_256.txt", "r")
hybit_data = file.readlines()
hybit_data = [float(i)*640 for i in hybit_data]
ax.plot([i for i in np.arange(-8, 8, 0.015625)], hybit_data[0:1024], color="purple")

ax.legend(["HyBit", "MCMC MH Run 1", "MCMC MH Run 2"])
ax.set_xlabel("mu1")
ax.set_ylabel("pr(mu1)")

fig.savefig("results/multimodal_mcmc_mh.pdf", bbox_inches='tight')

fig, ax = plt.subplots()
plt.rcParams["figure.figsize"] = [4.5, 4.50]
plt.rcParams.update({'font.size': 15})
plt.rc('xtick', labelsize=15)
plt.rc('ytick', labelsize=15)
plt.rc('axes', labelsize=20)
plt.rc('legend', fontsize=20)
plt.ylim(0, 18)
w = 0.1
scale_y = 100
ticks_y = ticker.FuncFormatter(lambda x, pos: '{0:g}'.format(x/scale_y))
ax.yaxis.set_major_formatter(ticks_y)

file1 = open("benchmarks/multimodal/result1SMC.txt", "r")
lines1 = file1.readlines(100000)
smc_samples = []
for i in lines1[1:-1]:
    curr = i.split(", ")
    for j in curr:
        smc_samples.append(float(j.strip(" ,\n")))
ax.hist(smc_samples, bins = np.arange(-6, 6 + w, w), alpha = 0.25, color="red")

file = open("benchmarks/multimodal/multimodal_6_256.txt", "r")
hybit_data = file.readlines()
hybit_data = [float(i)*640 for i in hybit_data[0:1024]]
ax.plot([i for i in np.arange(-8, 8, 0.015625)], hybit_data, color="purple")

ax.legend(["HyBit", "SMC Run"])
ax.set_xlabel("mu1")

fig.savefig("results/multimodal_smc.pdf", bbox_inches='tight')

file = open("benchmarks/multimodal/multimodal/analysis_mu1.txt")
data = file.readlines()
AQUA_x = data[5].split(',')[1:-3]
AQUA_x = [float(i) for i in AQUA_x]
AQUA_y = data[6].split(',')[1:-2]
AQUA_y = [float(i) for i in AQUA_y]

fig, ax = plt.subplots()
plt.rcParams["figure.figsize"] = [4.50, 4.50]
plt.rcParams.update({'font.size': 15})
plt.rc('xtick', labelsize=15)
plt.rc('ytick', labelsize=15)
plt.rc('axes', labelsize=20)
plt.rc('legend', fontsize=20)
w = 0.1

file = open("benchmarks/multimodal/multimodal_6_256.txt", "r")
hybit_data = file.readlines()
hybit_data = [float(i)*640 for i in hybit_data[0:1024]]

ax.plot(AQUA_x, [y*0.8680*640 for y in AQUA_y]) # 0.8680 for same discretization interval
ax.plot([i for i in np.arange(-8, 8, 0.015625)], hybit_data, color="purple")

plt.ylim(0, 18)
ax.legend(["AQUA", "HyBit"], loc="upper left")
ax.set_xlabel("mu1")

scale_y = 100
ticks_y = ticker.FuncFormatter(lambda x, pos: '{0:g}'.format(x/scale_y))
ax.yaxis.set_major_formatter(ticks_y)

fig.savefig("results/multimodal_aqua.pdf", bbox_inches='tight')