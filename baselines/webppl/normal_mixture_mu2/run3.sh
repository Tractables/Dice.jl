for j in {1..40}
do
	for i in {1..10}
	do
       		echo $j	
		timeout 2000s /space/poorvagarg/webppl/webppl normal_mixture3.wppl --require webppl-timeit -- --s $((2**$j)) --m $1 >> output3_$1_$j.txt
	done
done
