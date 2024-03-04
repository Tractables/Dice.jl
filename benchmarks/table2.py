import numpy as np
import math
import sys
import statistics
import csv
from tabulate import tabulate

gt = {}
benchmarks = ["pi", "weekend", "spacex", "GPA", "tug_of_war", "altermu2", "conjugate_gaussians2", "normal_mixture_theta", "normal_mixture_mu1", "normal_mixture_mu2", "zeroone_w1", "zeroone_w2", "coinBias", "addFun_sum", "clickGraph", "trueskill", "clinicalTrial1", "clinicalTrial2", "addFun_max"]

gt["pi"] = (5 - math.pi)/4
gt["GPA"] = 0.6115107913669064
gt["tug_of_war"] = 0.5
gt["altermu2"] = 0.1550617483
gt["normal_mixture_theta"] = 12/42
gt["normal_mixture_mu1"] = -9.702359975571609
gt["normal_mixture_mu2"] = 9.657948191704119
gt["spacex"] = 30.00463476991299
gt["zeroone_w1"] = 0.0565823032448
gt["zeroone_w2"] = 3.68882559517
gt["weekend"] = 0.3742061754266954
gt["conjugate_gaussians2"] = 1.00
gt["coinBias"] = 5/12
gt["addFun_sum"] = 0.0
gt["clickGraph"] = 0.614154185582757
gt["addFun_max"] = 1/math.sqrt(math.pi)
gt["clinicalTrial2"] = 2/7
gt["clinicalTrial1"] = 1 - 78460907384924307566949191554862076141244676160/94572409612368043294199619316675018741649913883
gt["trueskill"] = 0.5

#due to the range not being [0, 1]
extra_bits = {}

extra_bits["pi"] = 2
extra_bits["GPA"] = 5
extra_bits["tug_of_war"] = 5
extra_bits["altermu2"] = 6
extra_bits["normal_mixture_theta"] = 6
extra_bits["normal_mixture_mu1"] = 6
extra_bits["normal_mixture_mu2"] = 6
extra_bits["spacex"] = 8
extra_bits["zeroone_w1"] = 8
extra_bits["zeroone_w2"] = 8
extra_bits["weekend"] = 4
extra_bits["conjugate_gaussians2"] = 8
extra_bits["coinBias"] = 2
extra_bits["addFun_sum"] = 5
extra_bits["clickGraph"] = 2
extra_bits["addFun_max"] = 5
extra_bits["clinicalTrial2"] = 2
extra_bits["clinicalTrial1"] = 2
extra_bits["trueskill"] = 6

table = []

for i in benchmarks:
    gt_index = -3
    if i == "normal_mixture_theta":
        file = open(f"benchmarks/normal_mixture/results_1.txt", "r")
    elif i == "normal_mixture_mu1":
        file = open(f"benchmarks/normal_mixture/results_2.txt", "r")
    elif i == "normal_mixture_mu2":
        file = open(f"benchmarks/normal_mixture/results_0.txt", "r")
    elif i == "zeroone_w1":
        file = open(f"benchmarks/zeroone/results_1.txt", "r")
    elif i == "zeroone_w2":
        file = open(f"benchmarks/zeroone/results_0.txt", "r")
    else:
        file = open(f"benchmarks/{i}/results.txt", "r")
        gt_index = -2
    
    l = file.readlines()
    data = l[0].split(",")
    bench = i
    error = abs(gt[i] - float(data[gt_index]))
    bits = float(data[0]) + extra_bits[i]

    if i in ["pi", "zeroone_w1", "zeroone_w2", "clickGraph", "clinicalTrial1", "clinicalTrial2"]:
        pieces = "-"
    else:
        pieces = float(data[1])
    table.append([bench, error, bits, pieces])
    # print(f"{bench} \t {error} \t {bits} \t {pieces}")

variables = {}

variables["pi"] = "answer"
variables["GPA"] = 5
variables["tug_of_war"] = "ans"
variables["altermu2"] = "mu[1]"
variables["normal_mixture_theta"] = "theta"
variables["normal_mixture_mu1"] = "mu[1]"
variables["normal_mixture_mu2"] = "mu[2]"
variables["spacex"] = "cr"
variables["zeroone_w1"] = "w1"
variables["zeroone_w2"] = "w2"
variables["weekend"] = ""
variables["conjugate_gaussians2"] = "mu"
variables["coinBias"] = "b"
variables["addFun_sum"] = "ans"
variables["clickGraph"] = "similarityAll"
variables["addFun_max"] = "ans"
variables["clinicalTrial2"] = "probIfControl"
variables["clinicalTrial1"] = "isEffective"
variables["trueskill"] = "final"

count = 0
for i in benchmarks:
    if i == "GPA" or i == "weekend":
        table[count].append("X")
        count += 1
        continue
    elif i in ["normal_mixture_theta", "normal_mixture_mu1", "normal_mixture_mu2"]:
        file_handle = open(f"baselines/stan/normal_mixture/results_1200.txt", "r")
    elif i in ["zeroone_w1", "zeroone_w2"]:
        file_handle = open(f"baselines/stan/zeroone/results_1200.txt", "r")
    else:
        file_handle = open(f"baselines/stan/{i}/results_1200.txt", "r")
    lines = file_handle.readlines()

    answer = 0
    for j in lines:
        current = j.split()
        if current != []:
            if current[0] == variables[i]:
                if i == "pi":
                    answer = 1 - float(current[1])
                elif i == "clinicalTrial1":
                    answer = float(current[1]) - 1
                else:
                    answer = float(current[1])
    error = abs(gt[i] - answer)
    table[count].append(error)
    count += 1
    # print(table[count-1])




print(tabulate(table))




