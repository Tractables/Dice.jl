def num_to_col(i):
    l, r = divmod(i, 26)
    l = '' if l == 0 else chr(ord('A') + l - 1)
    r = chr(ord('A') + r)
    return l + r

i = 1
green_cols = []
red_cols = []
while True:
    col = num_to_col(i)
    cols = green_cols if i % 2 == 1 else red_cols
    cols.append(f"{col}2:{col}1000")
    if col == "GU":
        break
    i += 1

print(','.join(green_cols))
print(','.join(red_cols))
