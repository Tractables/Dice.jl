for (( i=1; i<=10; i++))
do
    echo "$((5*$i))" >> baselines/psi/or/psi_or_results_new.txt
    timeout 1200s ./psi --expectation --raw baselines/psi/or/or_$((5*$i)).psi >> baselines/psi/or/psi_or_results_new.txt 
    echo "Completed $((5*$i))"
done