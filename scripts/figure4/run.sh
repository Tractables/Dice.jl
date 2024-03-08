julia --project benchmarks/multimodal/multimodal.jl
webppl benchmarks/multimodal/multimodal.wppl -- --s $((2**20)) --m MCMC >> benchmarks/multimodal/result_new1MCMC.txt
webppl benchmarks/multimodal/multimodal.wppl -- --s $((2**20)) --m MCMC >> benchmarks/multimodal/result_new2MCMC.txt
webppl benchmarks/multimodal/multimodal.wppl -- --s $((2**16)) --m SMC >> benchmarks/multimodal/result_new1SMC.txt

timeout 1200s benchmarks/multimodal/multimodal/multimodal sample num_samples=1000000 num_chains=2 data file=benchmarks/multimodal/multimodal/multimodal.data.R output file=benchmarks/multimodal/multimodal/multimodal_samples.csv
cd ../AQUA
java -cp "target/aqua-1.0.jar:lib/storm-1.0.jar" aqua.analyses.AnalysisRunner ../Dice.jl/benchmarks/multimodal/multimodal