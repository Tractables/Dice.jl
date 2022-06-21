using Dice
include("../util.jl")

# Put enum in module so case variables are scoped
module Terminals
    @enum Terminals_ ran saw Alice Bob and
end

# Specify probabilistic grammar
start_sym = "S"
rules = Dict(
    "S" =>  # LHS is always a single nonterminal
        [(["NP", "VP"], 1.0)],  # List of (RHS, probability) tuples
    "NP" =>
        [([Terminals.Alice], 0.4),
        ([Terminals.Bob], 0.4),
        (["NP", Terminals.and, "NP"], 0.2)],
    "VP" =>
        [(["V"], 0.7),
        (["V", "NP"], 0.3)],
    "V" =>
        [([Terminals.ran], 0.4),
        ([Terminals.saw], 0.6)]
)

# Prefix to check for
prefix = [Terminals.Alice, Terminals.and]

# Maximum depth parse tree to consider
num_steps = 4

# Probabilistically expand RHS until it is all terminals or the depth bound is reached.
# Returns (expansion, error), where error is true in execution paths where we hit
# the depth bound without being able to expand all nonterminals.
function expand_rhs(rhs, max_depth)
    expansion = DistVector{DistEnum}()
    err = DistFalse()
    for subterm in rhs
        x = expand_symbol(subterm, max_depth - 1)
        expansion = prob_extend(expansion, x[1])
        err |= x[2] 
    end
    expansion, err
end

# Probabilistically symbol until it is all terminals or the depth bound is met.
# Returns (expansion, error), where error is true in execution paths where we hit
# the depth bound without being able to expand all nonterminals.
function expand_symbol(sym, max_depth)
    # @dice_ite converts if/elseif/else to IfElse.ifelse
    @dice_ite if sym isa Terminals.Terminals_
        DistVector(DistEnum[DistEnum(sym)]), DistFalse()  # Terminal, no error
    elseif max_depth == 0
        DistVector{DistEnum}(), DistTrue()  # Unexpandable nonterminal, error
    else
        # Sample from expansion of rules
        discrete((expand_rhs(rhs, max_depth), p) for (rhs, p) in rules[sym])
    end
end

sentence, error = expand_symbol(start_sym, num_steps)
has_prefix = prob_startswith(sentence, to_dist(prefix))

# DWE ("dist with error") records error.
# sentence_dist is the distribution over sentences in execution paths where error is false.
# error_p is the probability error is true given observe.
sentence_dist, error_p = infer(DWE(sentence, error))
@assert sum(values(sentence_dist)) + error_p ≈ 1

# we already calculated error_p, so no need to wrap in a DWE again
# note that has_prefix_p undercounts, as we do not consider execution paths that error
has_prefix_p = infer_bool(has_prefix & !error)

# This would do the same thing, recalculating the same value for error_p:
# has_prefix_p, error_p = infer_bool(DWE(has_prefix, error))

println("Probability sentence starts with $(to_str_pretty(prefix)): $(has_prefix_p)")
println("Probability of error: $(error_p)")
println("Distribution over sentences:")
print_dict(sentence_dist)

#==
Probability sentence starts with [Alice, and]: 0.08425824255999999
Probability of error: 0.04876351487999998
Distribution over sentences:
   [Alice, saw]             => 0.168
   [Bob, saw]               => 0.168
   [Alice, ran]             => 0.11199999999999996
   [Bob, ran]               => 0.11199999999999996
   [Bob, saw, Alice]        => 0.02880000000000002
   [Bob, saw, Bob]          => 0.02880000000000002
   [Alice, saw, Alice]      => 0.028800000000000006
   [Alice, saw, Bob]        => 0.028800000000000006
   [Bob, ran, Bob]          => 0.01920000000000001
   [Bob, ran, Alice]        => 0.01920000000000001
   [Alice, ran, Alice]      => 0.0192
   [Alice, ran, Bob]        => 0.0192
   [Alice, and, Bob, saw]   => 0.013439999999999999
   [Alice, and, Alice, saw] => 0.013439999999999999
   [Bob, and, Alice, saw]   => 0.013439999999999987
   [Bob, and, Bob, saw]     => 0.013439999999999987
   [Bob, and, Alice, ran]   => 0.008960000000000017
   [Bob, and, Bob, ran]     => 0.008960000000000017
   [Alice, and, Alice, ran] => 0.008959999999999994
   [Alice, and, Bob, ran]   => 0.008959999999999994
   ⋮                        => ⋮
==#
