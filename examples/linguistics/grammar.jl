# Probabilistic Grammar - grammar.jl
#
# Given a probabilistic context-free grammar (rules are annotated with the
# probability that its LHS nonterminal will expand to it), finds the
# distribution over sentences it can generate, given that the sentence starts
# with a particular prefix.
#
# The height of the considered sentences' parse trees is bounded to `num_steps`,
# and the probability that this bound is exceeded is also calculated.

using Dice
include("./util.jl")

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
    if sym isa Terminals.Terminals_
        DistVector(DistEnum[DistEnum(sym)]), DistFalse()  # Terminal, no error
    elseif max_depth == 0
        DistVector{DistEnum}(), DistTrue()  # Unexpandable nonterminal, error
    else
        # Sample from expansion of rules
        discrete((expand_rhs(rhs, max_depth), p) for (rhs, p) in rules[sym])
    end
end

sentence, err = expand_symbol(start_sym, num_steps)
has_prefix = prob_startswith(sentence, to_dist(prefix))

# dist is the distribution over sentences in execution paths where error is false.
# error_p is the probability error is true.
dist, error_p = infer(sentence, err=err)
@assert sum(values(dist)) + error_p ≈ 1

# note that has_prefix_p undercounts, as we do not consider execution paths that error
has_prefix_p = infer_bool(has_prefix & !err)

# This does the same thing, recalculating the same value for error_p:
# inf_res = infer(has_prefix, err=err)
# has_prefix_p, error_p = inf_res[true], inf_res.error_p

println("Probability sentence starts with $(to_str_pretty(prefix)): $(has_prefix_p)")
println("Probability of error: $(error_p)")
println("Distribution over sentences:")
print_dict(dist)
comp_graphs = [sentence, err, has_prefix]
println("$(num_nodes(comp_graphs, suppress_warning=true)) nodes, $(num_flips(comp_graphs)) flips")

#==
Probability sentence starts with [Alice, and]: 0.08425824255999999
Probability of error: 0.048763514880000004
Distribution over sentences:
   [Bob, saw]               => 0.168
   [Alice, saw]             => 0.168
   [Bob, ran]               => 0.11199999999999996
   [Alice, ran]             => 0.11199999999999996
   [Alice, saw, Bob]        => 0.028800000000000006
   [Alice, saw, Alice]      => 0.028800000000000006
   [Bob, saw, Alice]        => 0.028800000000000006
   [Bob, saw, Bob]          => 0.028800000000000006
   [Alice, ran, Alice]      => 0.0192
   [Bob, ran, Alice]        => 0.0192
   [Bob, ran, Bob]          => 0.0192
   [Alice, ran, Bob]        => 0.0192
   [Bob, and, Bob, saw]     => 0.013439999999999999
   [Alice, and, Alice, saw] => 0.013439999999999999
   [Bob, and, Alice, saw]   => 0.013439999999999999
   [Alice, and, Bob, saw]   => 0.013439999999999999
   [Alice, and, Bob, ran]   => 0.008959999999999994
   [Bob, and, Alice, ran]   => 0.008959999999999994
   [Bob, and, Bob, ran]     => 0.008959999999999994
   [Alice, and, Alice, ran] => 0.008959999999999994
   ⋮                        => ⋮
150 nodes, 23 flips
==#
