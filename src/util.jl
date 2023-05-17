using Distributions

export gaussian_observe, gaussian_observe_enumerate, parametrised_flip, print_tree

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

# This API is for combining all the observations
function gaussian_observe_enumerate(::Type{DistFixedPoint{W, F}}, data, mu, sigma) where W where F
    for i = -2^(W-F-1):1/2^F:2^(W-F-1) - 1/2^F
        for j =  1/2^F:1/2^F:2^(W-F-1) - 1/2^F
            flip_prob = reduce(*, [pdf(Normal(i, j), datapt)/(10^5) for datapt in data])
            a = prob_equals(mu, DistFixedPoint{W, F}(i)) & prob_equals(sigma, DistFixedPoint{W, F}(j))
            # TODO: Verify the observed expression
            observe(!a | (a & flip(flip_prob)))
        end
    end
end

#We might want to inline this to interleave bits of p and new uniform
function parametrised_flip(p::DistFixedPoint{W, F}) where W where F
    invalid = (p < DistFixedPoint{W, F}(0.0)) | (DistFixedPoint{W, F}(1.0) < p)
    invalid && error("flip probability outside interval [0, 1]")

    uniform(DistFixedPoint{W, F}, 0.0, 1.0) < p
end

# Print a tree represented as a tuple of the form:
#   tree ::= (node, children::Vector{tree})
# If a non-tuple x is encountered, it is treated as the leaf (x, [])
function print_tree(t::Tuple; indent_per_level=4, io::IO=stdout)
    @assert indent_per_level >= 1
    print_tree_helper(t, Integer[], 0, false, indent_per_level, io)
end

function print_tree_helper(
    t,
    pipes::Vector{<:Integer},
    level::Integer,
    last_child::Bool,
    indent_per_level::Integer,
    io::IO
)
    if !(t isa Tuple)
        t = (t, [])
    end
    # Print padding
    padding_size = level * indent_per_level
    if level > 0
        padding = [' ' for _ in 1:padding_size]
        for pipe in pipes
            padding[pipe] = '│'
        end
        # Connect last pipe to value
        padding[last(pipes)] = if last_child '└' else '├' end
        for i in (last(pipes)+1):(padding_size-1)
            padding[i] = '─'
        end
        print(io, join(padding))
    end

    # Print value
    println(io, t[1])
    
    # Consume last pipe if we are last child, always create new pipe below us
    inherited_pipes = copy(pipes)
    if last_child
        pop!(inherited_pipes)
    end
    push!(inherited_pipes, padding_size + 1)

    for i in 1:length(t[2])
        print_tree_helper(
            t[2][i],
            inherited_pipes,
            level + 1,
            i == length(t[2]),
            indent_per_level,
            io
        )
    end
end