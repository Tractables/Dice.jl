using Plots
using DelimitedFiles

data_file = readdlm("./linear_regression.txt", ',', Float64)
xs = data_file[:, 2]
time = data_file[:, 3]

plot(xs, time, xlabel="No. of observations", ylabel="Time(s)", marker=:circle, title="Bayesian Linear Regression")
plot(xs, time, yaxis=:log, xlabel="No. of observations", ylabel="Time(s)", marker=:circle, title="Bayesian Linear Regression")