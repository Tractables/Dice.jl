# awk 'NR==1 {print; next} NR<=401 || (NR-1)%200==0' $1
awk 'NR<=400 || NR%200==0' $1
