for (( i=0; i<=20; i++))
do
    echo $i
    timeout 1200s java -cp "target/aqua-1.0.jar:lib/storm-1.0.jar" aqua.analyses.AnalysisRunner $1 $((2**$i))
    python3 benchmarks/aqua_data.py $2 >> $3
done
