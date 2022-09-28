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

function gaussian_observe(::Type{DistFixedPoint{W, F}}, pieces::Int, start::Float64, stop::Float64, mean::Float64, std::DistFixedPoint{W, F}, datapt::Float64; mult=true) where W where F
    #TODO: implement isless for fixedpoint to support the following check
    # isneg = DistFixedPoint{W, F}(0.0) < std
    # isneg && error("Standard deviation <= 0")

    g = continuous(DistFixedPoint{W, F}, Normal(mean, 1.0), pieces, start, stop)
    if mult
        observe(g*std == DistFixedPoint{W, F}(datapt))
    else
        observe(g == DistFixedPoint{W, F}(datapt) / std)
    end
end

function gaussian_observe(::Type{DistFixedPoint{W, F}}, pieces::Int, start::Float64, stop::Float64, mean::DistFixedPoint{W, F}, std::DistFixedPoint{W, F}, datapt::Float64; mult=true) where W where F
    #TODO: implement isless for fixedpoint to support the following check
    # isneg = DistFixedPoint{W, F}(0.0) < std
    # isneg && error("Standard deviation <= 0")

    g = continuous(DistFixedPoint{W, F}, Normal(0.0, 1.0), pieces, start, stop)
    if mult
        observe(g*std + mean == DistFixedPoint{W, F}(datapt))
    else
        observe(g == (DistFixedPoint{W, F}(datapt) - mean) / std)
    end
end

