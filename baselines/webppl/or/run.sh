for j in {20..40}
do
	for i in {1..5}
	do
       		echo $i	
		timeout 1200s /space/poorvagarg/webppl/webppl or_10.wppl --require webppl-timeit -- --s $((2**$j)) --m $1 >> output_$1_$j.txt
	done
done
