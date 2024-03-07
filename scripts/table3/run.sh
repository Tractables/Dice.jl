for i in baselines/psi/*.psi;do
    echo "Running $i"
    echo $i >> baselines/psi/results.txt
    timeout 1200s /space/poorvagarg/PLDI2023/psi/psi --expectation --raw --mathematica $i >> baselines/psi/results.txt
done
