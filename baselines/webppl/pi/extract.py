from statistics import mean, median, stdev
from scipy.special import rel_entr
import sys
import math
a = open("output_MCMC_" + sys.argv[1] + ".txt")
b = a.readlines()
c = []
for i in b:
    c.extend(i.split())

time = []
for i in range(len(c)):
    if c[i] == 'runtimeInMilliseconds:':
        time.append(float(c[i+1]))
#print("Estimated runtime: ", time/10)

ref= [(5 - math.pi)/4, 1 - (5 - math.pi)/4]
accuracy = []
for j in range(len(c)):
    if c[j] == 'value:':
	#print(c[j+2][:-1])
        temp = float(c[j+1][:-1])
        temp2 = sum(rel_entr(ref, [temp, 1 - temp]))
        accuracy.append(temp2)
print(median(time), median(accuracy), stdev(accuracy))

