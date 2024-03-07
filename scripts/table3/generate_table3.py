from tabulate import tabulate

file = open("baselines/psi/results.txt", "r")
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

    