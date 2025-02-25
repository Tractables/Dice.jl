mkdir temp_files
# setting TIMEFORMAT is suspicious
TIMEFORMAT='%3R'
for i in {2..10}
do
    echo "running for length $i"
    python3 gen_psi_luhn.py $i > temp_files/luhn_gen_$i.psi
    # for j in {1..5}
    # do
    time ( psi temp_files/luhn_gen_$i.psi > /dev/null ) 2>> psi_luhn.txt
    # done 
done
unset TIMEFORMAT
rm -r temp_files
