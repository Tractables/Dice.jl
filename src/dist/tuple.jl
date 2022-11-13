##################################
# inference
##################################

tobits(x::Tuple) = 
    mapreduce(tobits, vcat, x)

frombits(x::Tuple, world) = 
    map(v -> frombits(v, world), x)

tobits(x::Matrix) = 
    mapreduce(tobits, vcat, x)

frombits(x::Matrix, world) = 
    map(v -> frombits(v, world), x)

tobits(x::Matrix) = 
    mapreduce(tobits, vcat, x)

frombits(x::Matrix, world) = 
    map(v -> frombits(v, world), x)
Base.ifelse(cond::Dist{Bool}, then::Tuple, elze::Tuple) =
    Tuple(ifelse(cond, x, y) for (x, y) in zip(then,elze))
