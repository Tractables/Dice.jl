for j in {1..40}
do
	for i in {1..10}
	do
       		echo $i	
		timeout 2000s webppl clickGraph.wppl --require webppl-timeit -- --s $((2**$j)) --m $1 >> output_$1_$j.txt
	done
done
