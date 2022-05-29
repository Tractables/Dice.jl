export infer, group_infer, infer_with_observation, @Pr

# Efficient infer for any distribution for which group_infer is defined
function infer(d)
    ans = Dict()
    group_infer(d, true, 1.0) do assignment, _, p
        if haskey(ans, assignment)
            # If this prints, some group_infer implementation is probably inefficent.
            println("Warning: Multiple paths to same assignment.")
            ans[assignment] += p
        else
            ans[assignment] = p
        end
    end
    ans
end

macro Pr(code)
    # TODO: use MacroTools or similar to make this more flexible. It would be
    # to support arbitrary expressions, as long as they aren't ambiguous
    # (e.g. multiple |'s ) - or we use || instead of | for boolean or?
    msg = ("@Pr requires the form `@Pr(X)` or `Pr(X | Y)`. As an alternative to"
        * " the macro, consider `infer_with_observation(X, Y)`.")
    if code isa Symbol
        temp = gensym()
        return quote
            $temp = $(esc(code))
            if $temp isa DistBool || $temp isa DWE{DistBool}
                infer_bool($temp)
            else
                infer($temp)
            end
        end
    else
        @assert (length(code.args) == 3 && code.args[1] == :|) msg
        temp = gensym()
        return quote
            $temp = $(esc(code.args[2]))
            if $temp isa DistBool || $temp isa DWE{DistBool}
                infer_with_observation($temp, $(esc(code.args[3])))[true]
            else
                infer_with_observation($temp, $(esc(code.args[3])))
            end
        end
    end
end

function infer_with_observation(d::Dist, observation::DistBool)
    dist = Dict()
    group_infer(observation, true, 1.0) do observation_met, observe_prior, denom
        if !observation_met return end
        group_infer(d, observe_prior, denom) do assignment, _, p
            dist[assignment] = p/denom
        end
    end
    dist
end

# Workhorse for group_infer; it's DistBools all the way down
# Params:
#   d is the Dist to infer on
#   prior is a DistBool that must be satisfied
#   prior_p is Pr(prior)
# Behavior:
#   For each satisfying assignment x of d such that prior is true, calls f with:
#   x, a new_prior equivalent to (prior & (d = x)), and Pr(new_prior)
function group_infer(f, d::DistBool, prior, prior_p::Float64)
    new_prior = d & prior
    p = infer_bool(new_prior)
    if p != 0
        f(true, new_prior, p)
    end
    if !(p ≈ prior_p)
        f(false, !d & prior, prior_p - p)
    end
end

# We can infer a vector if we can infer the elements
function group_infer(f, vec::AbstractVector, prior, prior_p::Float64)
    if length(vec) == 0
        f([], prior, prior_p)
        return
    end
    group_infer(vec[1], prior, prior_p) do assignment, new_prior, new_p
        rest = @view vec[2:length(vec)]
        group_infer(rest, new_prior, new_p) do rest_assignment, rest_prior, rest_p
            assignments = vcat([assignment], rest_assignment)  # todo: try linkedlist instead
            f(assignments, rest_prior, rest_p)
        end
    end
end

# Defer to group_infer for vectors (which support @view, useful for efficiency)
function group_infer(f, tup::Tuple, prior, prior_p::Float64)
    group_infer(collect(tup), prior, prior_p) do vec_assignment, new_prior, p
        f(tuple(vec_assignment...), new_prior, p)
    end
end

bools(v::AbstractVector) =
    collect(Iterators.flatten(bools(x) for x in v))

bools(t::Tuple) =
    collect(Iterators.flatten(bools(x) for x in t))
