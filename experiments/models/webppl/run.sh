for i in {1..5}
do
	{ timeout 7200s /space/poorvagarg/node_modules/webppl/webppl $1.wppl --require webppl-timeit ; } >> /space/poorvagarg/.julia/dev/webppl_runs/$1.txt 
	
done
