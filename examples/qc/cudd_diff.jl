# Find the log-probabilities and the log-probability gradient of a BDD

# Calculate dict from BDD node to its log-probability
#   flip_probs: flip id -> probability
#   level_to_flip_id: CUDD level -> flip id
function logprob(
    bdds::Vector{CuddNode},
    flip_probs::Dict{<:Any, Float64},
    level_to_flip_id::Dict{<:Integer, <:Any},
    )
    cache = Dict{CuddNode,Float64}()
    terminal = get_one(bdds[1])
    cache[terminal] = log(one(Float64))
    cache[not(terminal)] = log(zero(Float64))

    rec(x) = 
        get!(cache, x) do
            i = level(x)
            f_id = level_to_flip_id[i]
            prob = flip_probs[f_id]
            a = log(prob) + rec(high(x))
            b = log(1.0-prob) + rec(low(x))
            if (!isfinite(a))
                b
            elseif (!isfinite(b))
                a
            else
                # log(exp(a) + exp(y))
                # https://www.wolframalpha.com/input?i=log%28e%5Ex%2Be%5Ey%29+-+%28max%28x%2C+y%29+%2B+log%281+%2B+e%5E%28-%7Cx-y%7C%29%29
                max(a,b) + log1p(exp(-abs(a-b)))
            end
        end
    
    for bdd in bdds
        rec(bdd)
    end
    cache
end

# Calculate gradient of a BDD node w.r.t. flip probabilities (reverse mode)
function grad_logprob(
    bdd::CuddNode,
    flip_probs::Dict{<:Any, Float64},
    level_to_flip_id::Dict{<:Integer, <:Any},
    logprobs::Dict{CuddNode, Float64},
)
    grad = Dict(f_id => 0.0 for f_id in keys(flip_probs))
    deriv = Dict{CuddNode, Float64}()
    deriv[bdd] = 1
    level_traversal(bdd) do node
        i, lo, hi = level(node), low(node), high(node)
        f_id = level_to_flip_id[i]
        f_prob = flip_probs[f_id]
        fhi, flo = logprobs[hi], logprobs[lo]
        get!(deriv, hi, 0)
        get!(deriv, lo, 0)
        denom = f_prob * exp(fhi) + (1 - f_prob) * exp(flo)
        deriv[hi] += deriv[node] * f_prob * exp(fhi) / denom
        deriv[lo] += deriv[node] * (1 - f_prob) * exp(flo) / denom
        grad[f_id] += deriv[node] * (exp(fhi) - exp(flo)) / denom
    end
    grad
end

# Calculate gradient of a BDD node w.r.t. flip probabilities (forward mode)
# Don't use this, it's slower
function grad_logprob_fwd(
    bdd::CuddNode,
    flip_probs::Dict{<:Any, Float64},
    level_to_flip_id::Dict{<:Integer, <:Any},
    logprobs::Dict{CuddNode, Float64},
)
    cache = Dict{CuddNode,Any}()
    zero_grad = Dict(f_id => 0.0 for f_id in keys(flip_probs))

    rec(x) =
        if is_constant(x)
            zero_grad
        else
            get!(cache, x) do
                @assert !is_constant(x)
                i, lo, hi = level(x), low(x), high(x)
                fhi = logprobs[hi]
                flo = logprobs[lo]
                f_id = level_to_flip_id[i]

                Dict(
                    p_f_id => begin
                        denom = param * exp(fhi) + (1 - param) * exp(flo)
                        if p_f_id == f_id
                            (exp(fhi) - exp(flo))/denom
                        else
                            (param * exp(fhi) * rec(hi)[p_f_id] + (1 - param) * exp(flo) * rec(lo)[p_f_id])/denom
                        end
                    end
                    for (p_f_id, param) in flip_probs
                )
            end
        end
    rec(bdd)
end

# Step flip probs in direction of gradient to maximize likelihood of BDDS
function step_flip_probs(
    flip_probs::Dict{<:Any, Float64},
    bdds_to_maximize::Vector{CuddNode},
    level_to_flip_id::Dict{<:Integer, <:Any},
    learning_rate::AbstractFloat
)
    total_grad = Dict(f_id => 0. for f_id in keys(flips))
    logprobs = logprob(bdds_to_maximize, flip_probs, level_to_flip_id)
    for bdd in bdds_to_maximize
        @assert !is_constant(bdd)
        total_grad += grad_logprob(bdd, flip_probs, level_to_flip_id, logprobs)
    end
    # Add as we want to maximize probability
    flip_probs = flip_probs + learning_rate * total_grad
    clamp!(flip_probs, 0, 1)
    flip_probs
end
