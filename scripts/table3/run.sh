for i in baselines/psi/*.psi;do
    echo "Running $i"
    echo $i >> baselines/psi/results.txt
    timeout 1200s psi --expectation --raw --mathematica $i >> baselines/psi/results.txt
done
