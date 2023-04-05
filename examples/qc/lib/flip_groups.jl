# Flips whose probability is shared via global dicts

# Map flip to group of flips that much share a probability
flip_to_group = Dict{Dice.Flip, Any}()

# Prob group to psp ("pre-sigmoid probability")
group_to_psp = Dict{Any, Float64}()

# flip_for(x) and flip_for(y) are always separate flips, but if x == y, then
# they share their probability.
function flip_for(group)
    f = flip(sigmoid(get!(group_to_psp, group, 0.)))
    flip_to_group[f] = group
    f
end