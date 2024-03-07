for i in {1..40}
do
	for j in {1..10}
	do
       		echo $i	
		timeout 2000s webppl conjugate_gaussians.wppl --require webppl-timeit -- --s $((2**$i)) --m $1 >> output_$1_$i.txt
	done
done
