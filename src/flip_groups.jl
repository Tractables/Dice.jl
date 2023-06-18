# Flips whose probabilities are parameterized by ADNodes

export get_parameterized_flips, get_flip_adnode,
    refresh_parameterized_flips!, clear_flips_and_params!, is_parameterized

# Map flip to group of flips that much share a probability
_flip_to_adnode = Dict{Dice.Flip, ADNode}()

function flip(p::ADNode)
    f = flip(nothing)
    _flip_to_adnode[f] = p
    f
end

get_parameterized_flips() = keys(_flip_to_adnode)
get_flip_adnode(f) = _flip_to_adnode[f]
is_parameterized(f) = haskey(_flip_to_adnode, f)

function refresh_parameterized_flips!()
    vals = compute(values(_flip_to_adnode))
    for (f, adnode) in _flip_to_adnode
        f.prob = vals[adnode]
    end
end

function clear_flips_and_params!()
    clear_params!()
    empty!(_flip_to_adnode)
end
