timeout 1200s ../multimodal/multimodal sample num_samples=1000000 num_chains=8 num_threads=4 data file=../multimodal/multimodal.data.R output file=../multimodal/multimodal_samples.csv
bin/stansummary -s 8 ../multimodal/multimodal_samples_1.csv > ../multimodal/results_1.txt
bin/stansummary -s 8 ../multimodal/multimodal_samples_2.csv > ../multimodal/results_2.txt
bin/stansummary -s 8 ../multimodal/multimodal_samples_3.csv > ../multimodal/results_3.txt
bin/stansummary -s 8 ../multimodal/multimodal_samples_4.csv > ../multimodal/results_4.txt
bin/stansummary -s 8 ../multimodal/multimodal_samples_5.csv > ../multimodal/results_5.txt
bin/stansummary -s 8 ../multimodal/multimodal_samples_6.csv > ../multimodal/results_6.txt
bin/stansummary -s 8 ../multimodal/multimodal_samples_7.csv > ../multimodal/results_7.txt
bin/stansummary -s 8 ../multimodal/multimodal_samples_8.csv > ../multimodal/results_8.txt