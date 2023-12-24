using Dice
include("util.jl")
include("dist_tree.jl")

# Put enum in module so case variables are scoped
module Syms
    @enum Syms_ S X Y a b c
end

# Specify probabilistic grammar
start_sym = Syms.S
rules = Dict(
    Syms.S =>  # LHS (always a single nonterminal)
        [([Syms.X], 0.6),  # List of (RHS, probability) tuples
        ([Syms.Y], 0.4)],
    Syms.X =>
        [([Syms.a, Syms.b, Syms.Y], 0.5),
        ([Syms.a], 0.5)],
    Syms.Y =>
        [([Syms.X, Syms.b, Syms.c], 0.3),
        ([Syms.c], 0.7)],
)

# Sentence to probabilistically parse
expected_sentence = DistVector(map(DistEnum, [Syms.a, Syms.b, Syms.c]))

# Maximum depth parse tree to consider
num_steps = 3

# Probabilistically generate syntax tree for rule (LHS and corresponding RHS)
# until all leaves are terminals or the depth bound is reached.
# Returns (tree, error), where error is true in execution paths where we hit
# the depth bound without being able to expand all nonterminal leaves.
function rule_to_tree(lhs, rhs, max_depth)
    # Put nonterminal at root
    expansion = DistBranch(DistEnum(lhs), DistVector([]))
    error = false
    for subterm in rhs
        # Children are trees for RHS symbols
        x = symbol_to_tree(subterm, max_depth - 1)
        expansion = prob_append_child(expansion, x[1])
        error |= x[2]
    end
    expansion, error
end

# Probabilistically generate syntax tree for symbol until all leaves are terminals
# or the depth bound is reached.
# Returns (tree, error), where error is true in execution paths where we hit the
# depth bound without being able to expand all nonterminal leaves.
function symbol_to_tree(sym, max_depth)
    if !haskey(rules, sym)  # sym is a terminal
        DistLeaf(DistEnum(sym)), false
    elseif max_depth == 0  # Reached max depth
        DistBranch(DistEnum(start_sym), DistVector([])), true  # Dummy node, just indicate that there is error
    else  # Choose from expansions with probabilities associated with their rules
        discrete((rule_to_tree(sym, rhs, max_depth), p) for (rhs, p) in rules[sym])    
    end
end

tree, err = symbol_to_tree(start_sym, num_steps)
sentence = leaves(tree)
@show pr(sentence, evidence=!err)
observe = prob_equals(sentence, expected_sentence)

# dist is the distribution over trees, excluding execution paths where err is true, given observe.
# error_p is the probability err is true given observe.
# Note: observe re-normalizes probabilities but error does not.
error_p = pr(err, evidence=observe)[true]
dist = Dict(fixup_tree(k) => v*(1-error_p) for (k, v) in pr(tree, evidence=observe & !err))
@assert sum(values(dist)) + error_p ≈ 1

println("Probability of error: $(error_p)")
println("Distribution over trees:")
print_dict(dist)

# To visualize trees:
example_tree = collect(dist)[2][1]
print_tree(example_tree)

#==
Probability of error: 0.0
Distribution over trees:
   (S, [(X, [(a, []), (b, []), (Y, [(c, [])])])]) => 0.7777777777777779
   (S, [(Y, [(X, [(a, [])]), (b, []), (c, [])])]) => 0.22222222222222224
20 nodes, 5 flips
S
└── X        
    ├── a    
    ├── b    
    └── Y    
        └── c
==#
