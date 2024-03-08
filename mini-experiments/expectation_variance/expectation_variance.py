import numpy as np
import math
import sys
import statistics
import csv
import matplotlib.pyplot as plt

filehandle = open("./mini-experiments/expectation_variance/exp_var_new.txt")
lines = filehandle.readlines()

plt.rcParams["figure.figsize"] = [5.50, 3.50]
plt.rcParams.update({'font.size': 15})
plt.rc('xtick', labelsize=15)
plt.rc('ytick', labelsize=15)
plt.rc('axes', labelsize=20)
plt.rc('legend', fontsize=15)

x = []
y1 = []
y2 = []
y3 = []
y4 = []
for i in lines[1:]:
    cur = i.split(",")
    x.append(int(float(cur[0])))
    y1.append(float(cur[1]))
    y2.append(float(cur[2]))
    y3.append(float(cur[3]))
    y4.append(float(cur[4]))

fig, ax = plt.subplots()
ax.set_yscale("log")
ax.set_xlabel("Bits")
ax.set_ylabel("Time (s)")
legend_list = ["Bitwise Expectation", "Naive Expectation"]

ax.scatter(x, y1, marker="o")
ax.scatter(x, y3, marker = "s")

ax.legend(legend_list, loc="upper left")
fig.savefig("results/exp_results.png", dpi=300, bbox_inches="tight")

fig, ax = plt.subplots()
ax.set_yscale("log")
ax.set_xlabel("Bits")
ax.set_ylabel("Time (s)")
legend_list = ["Bitwise Expectation", "Naive Expectation"]

ax.scatter(x, y2, marker="o")
ax.scatter(x, y4, marker = "s")

ax.legend(legend_list, loc="upper left")
fig.savefig("results/var_results.png", dpi=300, bbox_inches="tight")

