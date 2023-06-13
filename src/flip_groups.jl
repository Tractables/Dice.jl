# Flips whose probability is shared via global dicts

export flip_for, get_group_probs, reset_flips!, get_group_prob, propagate_group_probs!



# flip_for(x) and flip_for(y) are always separate flips, but if x == y, then
# they share their probability.
function flip_for(group, init_pr=0.5)
    # pr = if haskey(_group_to_psp, group) sigmoid
    f = flip(
        sigmoid(
            get!(_group_to_psp, group, inverse_sigmoid(init_pr))
        ),
        name="f_for($(group))")
    _flip_to_group[f] = group
    f
end

function get_group_probs()
	Dict(group => sigmoid(psp) for (group, psp) in _group_to_psp)
end

function get_group_prob(group)
    sigmoid(_group_to_psp[group])
end

function reset_flips!()
    global _flip_to_group = Dict{Dice.Flip, Any}()
    global _group_to_psp = Dict{Any, Float64}()
end

function propagate_group_probs!()
    for (f, group) in _flip_to_group
        f.prob = sigmoid(_group_to_psp[group])
    end
end
