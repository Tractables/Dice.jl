using Distributions

export gaussian_observe

##################################
# Gaussian observation methods
##################################

function gaussian_observe(::Type{DistFixedPoint{W, F}}, pieces::Int, start::Float64, stop::Float64, mean::Float64, std::Float64, datapt::DistFixedPoint{W, F}) where W where F
    @assert std > 0
    g = continuous(DistFixedPoint{W, F}, Normal(mean, std), pieces, start, stop)
    observe(g == datapt)
end

function gaussian_observe(::Type{DistFixedPoint{W, F}}, pieces::Int, start::Float64, stop::Float64, mean::DistFixedPoint{W, F}, std::Float64, datapt::DistFixedPoint{W, F}; add=true) where W where F
    @assert std > 0
    g = continuous(DistFixedPoint{W, F}, Normal(0.0, std), pieces, start, stop)
    
    if add
        observe(g + mean == datapt)
    else
        observe(g == datapt - mean)
    end
end

function gaussian_observe(::Type{DistFixedPoint{W, F}}, pieces::Int, start::Float64, stop::Float64, mean::Float64, std::DistFixedPoint{W, F}, datapt::DistFixedPoint{W, F}; mult=true) where W where F
    #TODO: implement isless for fixedpoint to support the following check
    # isneg = DistFixedPoint{W, F}(0.0) < std
    # isneg && error("Standard deviation <= 0")

    g = continuous(DistFixedPoint{W, F}, Normal(mean, 1.0), pieces, start, stop)
    if mult
        observe(g*std == datapt)
    else
        observe(g == datapt / std)
    end
end

function gaussian_observe(::Type{DistFixedPoint{W, F}}, pieces::Int, start::Float64, stop::Float64, mean::DistFixedPoint{W, F}, std::DistFixedPoint{W, F}, datapt::DistFixedPoint{W, F}; mult=true) where W where F
    #TODO: implement isless for fixedpoint to support the following check
    # isneg = DistFixedPoint{W, F}(0.0) < std
    # isneg && error("Standard deviation <= 0")

    g = continuous(DistFixedPoint{W, F}, Normal(0.0, 1.0), pieces, start, stop)
    if mult
        observe(g*std + mean == datapt)
    else
        observe(g == (datapt - mean) / std)
    end
end

# function gaussian_observe_enumerate(::Type{DistFixedPoint{W, F}}, mean, sigma, data; mean_min=-2^(W-F-1), mean_max=2^(W-F)-1/2^F, sigma_min=1/2^F, sigma_max=2^(W-F)-1/2^F) where W where F
#     @assert sigma_min > 0
#     @assert mean_max > mean_min
#     @assert sigma_max > sigma_min
#     for i = mean_min: 1/2^F: mean_max
#         for j = sigma_min: 1/2^F: sigma_max
#             flip_prob = reduce(*, [pdf(Normal(i, j), datapt)*10^(-3) for datapt in data])
#             observe(flip(flip_prob))
#         end
#     end
# end
