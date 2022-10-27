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