# HEADER:
awk 'NR==1 {print; next} NR<=401 || (NR-1)%200==0' $1

# NO HEADER:
# awk 'NR<=400 || NR%200==0' $1
