import json
import numpy as np

with open("/home/poorvagarg/Desktop/AQUA/benchmarks/stan_bench/altermu2/analysis_mu[1].txt", "r") as read_file:
    data = json.load(read_file)

true_variance = 20.50147795323516
true_mean = 0.151251662585150465

a = data["data"]
b = sum(np.multiply(a[1], a[0]))

c = sum(np.multiply(a[0], np.multiply(a[0], a[1]))) - b^2

with open("AQUA_altermu2_res.txt", "a") as write_file:
    write_file(abs(true_variance - mean))