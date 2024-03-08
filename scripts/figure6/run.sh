julia --project benchmarks/conjugate_gaussians/conjugate_gaussians.jl
webppl benchmarks/conjugate_gaussians/conjugate_gaussians.wppl -- --s $((2**20)) --m MCMC >> benchmarks/conjugate_gaussians/result_new1MCMC.txt
webppl benchmarks/conjugate_gaussians/conjugate_gaussians.wppl -- --s $((2**16)) --m SMC >> benchmarks/conjugate_gaussians/result_new1SMC.txt

cd ../AQUA
java -cp "target/aqua-1.0.jar:lib/storm-1.0.jar" aqua.analyses.AnalysisRunner benchmarks/conjugate_gaussians/conjugate_gaussians_aqua