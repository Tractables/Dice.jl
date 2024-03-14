for i in baselines/psi/*.psi;do
    echo "Running $i"
    touch $i.m
    echo "N[" > $i.m
    timeout 1200s /space/poorvagarg/PLDI2023/psi/psi --expectation --raw --mathematica $i >> $i.m
    echo ",10]" >> $i.m
    echo $i-results.txt
    timeout 1200s /space/poorvagarg/Mathematica14/Executables/math < $i.m > $i-results.txt
done
