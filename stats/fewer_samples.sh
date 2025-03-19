# HEADER:
awk 'NR==1 {print "Samples\t" $0; next} {print NR-1 "\t" $0}' $1 | awk 'NR==1 {print; next} NR<=401 || (NR-1)%200==0'

# NO HEADER:
# awk 'NR<=400 || NR%200==0' $1
