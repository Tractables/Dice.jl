import sys
import json
import numpy as np

def read_AQUA_file(filename):
    AQUA_file = open(filename, "r")
    AQUA_data = json.load(AQUA_file)
    res = AQUA_data['data']

    #plt.plot(res[0], res[1])
    #print(min(res[0]), max(res[0]))

    AQUA_mean = (sum(np.multiply(res[0], res[1])))
    #AQUA_variance = sum(np.multiply(np.square(res[0]), res[1])) - AQUA_mean**2
    print(AQUA_mean)
    #return AQUA_mean, AQUA_variance

read_AQUA_file(sys.argv[1])
