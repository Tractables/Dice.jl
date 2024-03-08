import numpy as np
import math
import sys
import statistics
import csv
import matplotlib.pyplot as plt

added = "_new"
if len(sys.argv) > 1:
    added = ""


def open_suffix(filename, tag="r"):
    f = filename.replace("results", "results" + added)
    try:
        file_handle = open(f, tag)
    except:
        file_handle = open(filename, tag)
    return file_handle

gt = {}
gt["altermu2"] = 0.1550617483
gt["addFun_max"] = 1/math.sqrt(math.pi)
gt["spacex"] = 30.00463476991299
gt["weekend"] = 0.3742061754266954

benchmark_name = "weekend"
bits = 6
pieces = 4
plt.rcParams["figure.figsize"] = [5.50, 3.50]
plt.rcParams.update({'font.size': 15})
plt.rc('xtick', labelsize=15)
plt.rc('ytick', labelsize=15)
plt.rc('axes', labelsize=20)
plt.rc('legend', fontsize=10)

def plot_fig8_time(benchmark_name, pieces, ylabel, ll, ul):
    filehandle = open_suffix("benchmarks/" + benchmark_name + "/full_results.txt")
    lines = filehandle.readlines()
    bits = int(float(lines[-1].split(",")[0]))
    fig, ax = plt.subplots()
    ax.set_xscale("log", base=2)
    # ax.set_yscale("log")
    ax.set_xlabel("# Linear Pieces")
    if ylabel:
        ax.set_ylabel("Time (s)")
    ax.set_title(benchmark_name)
    legend_list = []
    for i in range(ll, ul):
        cur = []
        for j in lines:
            if int(float(j.split(",")[0])) == i:
                cur.append(j)
        
        x = []
        y = []
        for j in cur:
            cur_split = j.split(",")
            x.append(int(float(cur_split[1])))
            y.append((float(cur_split[-1])))
        ax.plot(x, y)
        legend_list.append("b = " + str(i))
    ax.legend(legend_list, loc="upper left")
    fig.savefig("results/" + benchmark_name + " time.png", dpi=300, bbox_inches="tight")

def plot_fig8_result(benchmark_name, pieces, ylabel, ll, ul):
    filehandle = open_suffix("benchmarks/" + benchmark_name + "/full_results.txt")
    lines = filehandle.readlines()
    bits = int(float(lines[-1].split(",")[0]))
    fig, ax = plt.subplots()
    ax.set_xscale("log", base=2)
    ax.set_yscale("log")
    ax.set_xlabel("# Linear Pieces")
    if ylabel:
        ax.set_ylabel("Result (s)")
    ax.set_title(benchmark_name)
    legend_list = []
    for i in range(ll, ul):
        cur = []
        for j in lines:
            if int(float(j.split(",")[0])) == i:
                cur.append(j)
        
        x = []
        y = []
        for j in cur:
            cur_split = j.split(",")
            x.append(int(float(cur_split[1])))
            y.append(abs((float(cur_split[-2]))- gt[benchmark_name]))
        ax.plot(x[1:], y[1:])
        legend_list.append("b = " + str(i))
    ax.legend(legend_list, loc="upper right")
    fig.savefig("results/" + benchmark_name + " result.png", dpi=300, bbox_inches="tight")

plot_fig8_time("altermu2", pieces, False, 5, 11)
plot_fig8_result("altermu2", pieces, False, 5, 11)

plot_fig8_time("addFun_max", pieces, False, 13, 19)
plot_fig8_result("addFun_max", pieces, False, 13, 19)

plot_fig8_time("spacex", pieces, False, 6, 11)
plot_fig8_result("spacex", pieces, False, 6, 11)

plot_fig8_time("weekend", pieces, False, 15, 20)
plot_fig8_result("weekend", pieces, False, 15, 20)
