using Distributions

export gaussian_observe

##################################
# Gaussian observation methods
##################################

function gaussian_observe(::Type{DistFixedPoint{W, F}}, pieces::Int, start::Float64, stop::Float64, mean::Float64, std::Float64, datapt::Float64) where W where F
    @assert std > 0
    g = continuous(DistFixedPoint{W, F}, Normal(mean, std), pieces, start, stop)
    observe(g == DistFixedPoint{W, F}(datapt))
end

function gaussian_observe(::Type{DistFixedPoint{W, F}}, pieces::Int, start::Float64, stop::Float64, mean::DistFixedPoint{W, F}, std::Float64, datapt::Float64; add=true) where W where F
    @assert std > 0
    g = continuous(DistFixedPoint{W, F}, Normal(0.0, std), pieces, start, stop)
    
    if add
        observe(g + mean == DistFixedPoint{W, F}(datapt))
    else
        observe(g == DistFixedPoint{W, F}(datapt) - mean)
    end
end

