for j in {15..25}
do
	for i in {1..5}
	do
       	echo $i	
		timeout 1200s /space/poorvagarg/webppl/webppl or_$1/or_$1.wppl --require webppl-timeit -- --s $((2**$j)) --m $2 >> or_$1/output_$2_$j.txt
	done
done
