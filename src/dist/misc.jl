prob_all(xs) = reduce(&, xs; init=true)

##################################
# Nothing
##################################

tobits(::Nothing) = []
frombits(::Nothing, _) = nothing

##################################
# Tuple
##################################

tobits(x::Tuple) = 
    mapreduce(tobits, vcat, x; init=[])

frombits(x::Tuple, world) = 
    map(v -> frombits(v, world), x)

frombits_as_dist(x::Tuple, world) =
    map(v -> frombits_as_dist(v, world), x)

Base.ifelse(cond::Dist{Bool}, then::Tuple, elze::Tuple) =
    Tuple(ifelse(cond, x, y) for (x, y) in zip(then,elze))

function prob_equals(x::Tuple, y::Tuple)
    @assert length(x) == length(y)
    prob_all(prob_equals(a, b) for (a, b) in zip(x, y))
end

tobits(x::Vector) = 
    collect(Iterators.flatten(map(tobits, x)))

frombits(x::Vector, world) = 
    map(v -> frombits(v, world), x)

frombits_as_dist(x::Vector, world) =
    map(v -> frombits_as_dist(v, world), x)

Base.ifelse(cond::Dist{Bool}, then::Vector, elze::Vector) =
    [ifelse(cond, x, y) for (x, y) in zip(then,elze)]

function prob_equals(x::Vector, y::Vector)
    @assert length(x) == length(y)
    prob_all(prob_equals(a, b) for (a, b) in zip(x, y))
end


