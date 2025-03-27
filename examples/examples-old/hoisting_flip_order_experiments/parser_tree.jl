using Alea
using Alea: num_flips, num_nodes, DWE
using Revise
include("../util.jl")

@enum Symbols S X Y a b c

function tree()
    terminals = [a, b, c]

    rules = Dict([
        (S,  # LHS (always a single nonterminal)
            [([X], 0.6),  # Potential RHS, probability
            ([Y], 0.4)]),
        (X,
            [([a, b, Y], 0.5),
            ([a], 0.5)]),
        (Y,
            [([X, b, c], 0.3),
            ([c], 0.7)]),
    ])

    start_term = S
    num_steps = 3
    top_n = 40  # Only the top_n most likely strings are printed
    expected_sentence = [a, b, c]

    # @enum Symbols ran saw Alice Bob and S NP VP V
    # terminals = [Alice, Bob, and, ran, saw]

    # rules = Dict([
    #     (S,  # LHS (always a single nonterminal)
    #         [([NP, VP], 1.0)]), # Potential RHS, probability
    #     (NP,
    #         [([Alice], 0.4),
    #         ([Bob], 0.4),
    #         ([NP, and, NP], 0.2)]),
    #     (VP,
    #         [([V], 0.7),
    #         ([V, NP], 0.3)]),
    #     (V,
    #         [([ran], 0.4),
    #         ([saw], 0.6)])
    # ])

    # start_term = S
    # num_steps = 4
    # top_n = 40  # Only the top_n most likely strings are printed
    # expected_sentence = [Alice, and, Bob, and, Alice, saw, Bob]

    tree, tree_observe = @dice_ite begin
        function expand_term(lhs, max_depth)
            if lhs in terminals
                DistTree(DistEnum(lhs))
            elseif max_depth == 0
                Alea.DWE(DistTree(DistEnum(start_term)), flip(true))  # Dummy node, just indicate that there is error
            else
                expansions = []
                for (rhs, p) in rules[lhs]
                    expansion = DistTree(DistEnum(lhs))
                    for subterm in rhs
                        expansion = prob_append_child(expansion, expand_term(subterm, max_depth - 1))
                    end
                    push!(expansions, expansion)
                end
                
                # Find flip weights
                v = Vector(undef, length(rules[lhs]))
                s = 1.
                for (i, (rhs, p)) in reverse(collect(enumerate(rules[lhs])))
                    v[i] = p/s
                    s -= p
                end

                # Choose rhs
                rhs = expansions[1]
                for i in 2:length(rules[lhs])
                    f = flip(v[i])
                    rhs = if f expansions[i] else rhs end
                end
                rhs
            end
        end
        tree = expand_term(start_term, num_steps)
        sentence = leaves(tree)
        observe = prob_equals(sentence, DistVector([DistEnum(term) for term in expected_sentence]))
        tree, observe.d  # discard the error for the observe
    end
    tree, tree_observe
end
# dist, error_p = @Pr(tree | observe)
# println("Probability of error: $(error_p)")
# print_dict(dist)
# println("$(num_nodes([tree, observe])) nodes, $(num_flips([tree, observe])) flips")

# To visualize trees:
# example_tree = collect(dist)[1][1]
# print_tree(example_tree)

#==
Probability of error: 0.0
Vector{Tuple{String, Float64}} with 2 entries
   S Any[(X, Any[(a, Any[]), (b, Any[]), (Y, Any[(c, Any[])])])] => 0.7777777777777779
   S Any[(Y, Any[(X, Any[(a, Any[])]), (b, Any[]), (c, Any[])])] => 0.22222222222222224
28 nodes, 7 flips
==#