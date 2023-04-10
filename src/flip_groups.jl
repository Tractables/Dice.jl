# Flips whose probability is shared via global dicts

export flip_for, get_group_probs, reset_flips!, update_group_to_psp!

# Map flip to group of flips that much share a probability
_flip_to_group = Dict{Dice.Flip, Any}()

# Prob group to psp ("pre-sigmoid probability")
_group_to_psp = Dict{Any, Float64}()

# flip_for(x) and flip_for(y) are always separate flips, but if x == y, then
# they share their probability.
function flip_for(group)
    f = flip(sigmoid(get!(_group_to_psp, group, 0.)))
    _flip_to_group[f] = group
    f
end

function get_group_probs()
	Dict(group => sigmoid(psp) for (group, psp) in _group_to_psp)
end

function reset_flips!()
	empty!(_flip_to_group)
    empty!(_group_to_psp)
end

function update_group_to_psp!(group_to_psp::Dict{Any, Float64})
    global _group_to_psp
    _group_to_psp = group_to_psp
end