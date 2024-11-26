using Distributions
using LogExpFunctions

function linear_model(X, y)
    n, p = size(X)
    ws = rand(Normal(0, sqrt(2)), p)
    logscore = logpdf(MvNormal(X*ws, Diagonal([1 for i in 1:n])), y)
    return ws[1], logscore
end