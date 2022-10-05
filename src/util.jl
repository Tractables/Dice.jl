using Distributions

export gaussian_observe, parametrised_flip

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

# TODO: think about this API a bit more to get uniform usage
# function gaussian_observe_enumerate(::Type{DistFixedPoint{W, F}}, data, fmean, fstd, bounds) where W where F
#     # TODO: Is there a way to check if standard deviation is positive?
#     DFiP = DistFixedPoint{W, F}
#     a = Vector(undef, length(bounds))
#     s_list = Vector(undef, length(bounds))
#     for i=1:length(bounds)
#         t = bounds[i]
#         a[i] = t[2]:1/2^F:t[3] - 1/2^F
#         s_list[i] = t[1]
#     end
#     for k in Iterators.product(a...)
#         l = reduce(&, [prob_equals(s, DFiP(k_element)) for (s, k_element) in zip(s_list, k)])
#         if l
#             observe(reduce(*, [pdf(Normal(fmean(k...), fstd(k...)), datapt)*10^(-3) for datapt in data]))
#         end
#     end
# end

#We might want to inline this to interleave bits of p and new uniform
function parametrised_flip(p::DistFixedPoint{W, F}) where W where F
    invalid = (p < DistFixedPoint{W, F}(0.0)) | (DistFixedPoint{W, F}(1.0) < p)
    invalid && error("flip probability outside interval [0, 1]")

    uniform(DistFixedPoint{W, F}, 0.0, 1.0) < p
end