using Distributions

export gaussian_observe, gaussian_observe_enumerate, parametrised_flip

##################################
# Gaussian observation methods
##################################

function gaussian_observe(::Type{DistFix{W, F}}, pieces::Int, start::Float64, stop::Float64, mean::Float64, std::Float64, datapt::DistFix{W, F}) where W where F
    @assert std > 0
    g = continuous(DistFix{W, F}, Normal(mean, std), pieces, start, stop)
    observe(g == datapt)
end

function gaussian_observe(::Type{DistFix{W, F}}, pieces::Int, start::Float64, stop::Float64, mean::DistFix{W, F}, std::Float64, datapt::DistFix{W, F}; add=true) where W where F
    @assert std > 0
    g = continuous(DistFix{W, F}, Normal(0.0, std), pieces, start, stop)
    
    if add
        observe(g + mean == datapt)
    else
        observe(g == datapt - mean)
    end
end

function gaussian_observe(::Type{DistFix{W, F}}, pieces::Int, start::Float64, stop::Float64, mean::Float64, std::DistFix{W, F}, datapt::DistFix{W, F}; mult=true) where W where F
    #TODO: implement isless for fixedpoint to support the following check
    # isneg = DistFix{W, F}(0.0) < std
    # isneg && error("Standard deviation <= 0")

    g = continuous(DistFix{W, F}, Normal(mean, 1.0), pieces, start, stop)
    if mult
        observe(g*std == datapt)
    else
        observe(g == datapt / std)
    end
end

function gaussian_observe(::Type{DistFix{W, F}}, pieces::Int, start::Float64, stop::Float64, mean::DistFix{W, F}, std::DistFix{W, F}, datapt::DistFix{W, F}; mult=true) where W where F
    #TODO: implement isless for fixedpoint to support the following check
    # isneg = DistFix{W, F}(0.0) < std
    # isneg && error("Standard deviation <= 0")

    g = continuous(DistFix{W, F}, Normal(0.0, 1.0), pieces, start, stop)
    if mult
        observe(g*std + mean == datapt)
    else
        observe(g == (datapt - mean) / std)
    end
end

# This API is for combining all the observations
function gaussian_observe_enumerate(::Type{DistFix{W, F}}, data, mu, sigma) where W where F
    for i = -2^(W-F-1):1/2^F:2^(W-F-1) - 1/2^F
        for j =  1/2^F:1/2^F:2^(W-F-1) - 1/2^F
            flip_prob = reduce(*, [pdf(Normal(i, j), datapt)/(10^5) for datapt in data])
            a = prob_equals(mu, DistFix{W, F}(i)) & prob_equals(sigma, DistFix{W, F}(j))
            # TODO: Verify the observed expression
            observe(!a | (a & flip(flip_prob)))
        end
    end
end

#We might want to inline this to interleave bits of p and new uniform
function parametrised_flip(p::DistFix{W, F}) where W where F
    invalid = (p < DistFix{W, F}(0.0)) | (DistFix{W, F}(1.0) < p)
    invalid && error("flip probability outside interval [0, 1]")

    uniform(DistFix{W, F}, 0.0, 1.0) < p
end