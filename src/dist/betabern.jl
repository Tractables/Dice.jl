
export BetaBern

# BetaBern functions 
mutable struct BetaBern 
    alphas::Vector{DistUInt32} # params (length n-1, where n is number of possible values)
    total::Int # running sum of all params
    initial::Vector{Int} # initial values (length n)
end