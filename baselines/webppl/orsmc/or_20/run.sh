for j in {15..30}
do
	for i in {1..5}
	do
       		echo $i	
		timeout 2000s /space/poorvagarg/webppl/webppl or_20.wppl --require webppl-timeit -- --s $((2**$j)) --m $1 >> output_$1_$j.txt
	done
done
