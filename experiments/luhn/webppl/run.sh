for i in {2..10}
do
    echo "running for length $i"
    webppl luhn.wppl --require webppl-timeit -- --n $i >> webppl_luhn.txt
done