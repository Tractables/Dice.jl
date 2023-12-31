import sys

benchmark = sys.argv[1]
print(benchmark)
method = sys.argv[2]
number = sys.argv[3]
file_handle = open(benchmark + "/output_" + method + "_" + number + ".txt", "r")

ans = []
lines = file_handle.readlines()
for i in lines:
    if i.split()[0] == "{":
        a = 
