import sys
import json
import numpy as np

filenames = {"GPA": "analysis_n", "altermu2": "analysis_mu[1]", "conjugate_gaussians": "analysis_mu",
             "normal_mixture": "analysis_theta", "zeroone": "analysis_w1", "coinBias": "analysis_mu"}

def read_AQUA_file(filename):
    if filename == "normal_mixture":
        AQUA_file = open(f"/space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/{filename}/analysis_theta.txt", "r")
        AQUA_data = json.load(AQUA_file)
        res = AQUA_data['data']

        AQUA_mean = (sum(np.multiply(res[0], res[1])))
        a = open(f"/space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/{filename}/results_new.txt", "a")
        a.write(str(AQUA_mean)+"\n")
        a.close()

        AQUA_file = open(f"/space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/{filename}/analysis_mu[1].txt", "r")
        AQUA_data = json.load(AQUA_file)
        res = AQUA_data['data']

        AQUA_mean = (sum(np.multiply(res[0], res[1])))
        a = open(f"/space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/{filename}/results1_new.txt", "a")
        a.write(str(AQUA_mean)+"\n")
        a.close()

        AQUA_file = open(f"/space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/{filename}/analysis_mu[2].txt", "r")
        AQUA_data = json.load(AQUA_file)
        res = AQUA_data['data']

        AQUA_mean = (sum(np.multiply(res[0], res[1])))
        a = open(f"/space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/{filename}/results2_new.txt", "a")
        a.write(str(AQUA_mean)+"\n")
        a.close()
    elif filename == "zeroone":
        AQUA_file = open(f"/space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/{filename}/analysis_w1.txt", "r")
        AQUA_data = json.load(AQUA_file)
        res = AQUA_data['data']

        AQUA_mean = (sum(np.multiply(res[0], res[1])))
        a = open(f"/space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/{filename}/results_new.txt", "a")
        a.write(str(AQUA_mean)+"\n")
        a.close()

        AQUA_file = open(f"/space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/{filename}/analysis_w2.txt", "r")
        AQUA_data = json.load(AQUA_file)
        res = AQUA_data['data']

        AQUA_mean = (sum(np.multiply(res[0], res[1])))
        a = open(f"/space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/{filename}/results1_new.txt", "a")
        a.write(str(AQUA_mean)+"\n")
        a.close()

    else:

        AQUA_file = open(f"/space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/{filename}/{filenames[filename]}.txt", "r")
        AQUA_data = json.load(AQUA_file)
        res = AQUA_data['data']

        #plt.plot(res[0], res[1])
        #print(min(res[0]), max(res[0]))

        AQUA_mean = (sum(np.multiply(res[0], res[1])))
        #AQUA_variance = sum(np.multiply(np.square(res[0]), res[1])) - AQUA_mean**2

        a = open(f"/space/poorvagarg/.julia/dev/Dice.jl/baselines/aqua/{filename}/results_new.txt", "a")
        a.write(str(AQUA_mean)+"\n")
        a.close()
        #return AQUA_mean, AQUA_variance

read_AQUA_file(sys.argv[1])
