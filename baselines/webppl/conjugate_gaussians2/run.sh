for i in {10..40}
do
	for j in {1..5}
	do
       		echo $i	
		timeout 2000s /space/poorvagarg/webppl/webppl conjugate_gaussians.wppl --require webppl-timeit -- --s $((2**$i)) --m $1 >> output_$1_$i.txt
	done
done
