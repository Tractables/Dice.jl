using LinearAlgebra

function ground_truth_linear(X, y, prior_var, sigma_ll)
    S = Diagonal(prior_var)
    sigma = inv((transpose(X) * X) + inv(S))
    mu = sigma * transpose(transpose(y) * X)./(sigma_ll)
    mu, sigma
end

# X, y, beta = generate_linear(100, 1000)

# mu, sigma = ground_truth_linear(X, y, [2 for _ in 1:p], 1)