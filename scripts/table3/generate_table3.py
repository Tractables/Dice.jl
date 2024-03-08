from tabulate import tabulate
import sys

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

file = open_suffix("baselines/psi/results.txt", "r")
lines = file.readlines()

table = []
for i in range(len(lines)):
    cur_line = lines[i]
    if i == len(lines) - 1:
        if cur_line[-4:-1] == "psi":
            next_line = "psii"
        else:
            continue
    else:
        next_line = lines[i+1]

    if cur_line[-4:-1] == "psi":
        cur_file = cur_line
    else:
        continue

    if next_line[-4:-1] == "psi":
        res = "X"
    else:
        res = "YES"

    table.append([cur_file, res])

print(tabulate(table))

    