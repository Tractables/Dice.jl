using Dice
using Dice: num_flips, num_nodes
using Revise
include("util.jl")

@enum Symbols S X Y a b c
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
num_steps = 4
top_n = 40  # Only the top_n most likely strings are printed
expected_sentence = [a, b, c]

code = @dice begin
    function expand_term(lhs, max_depth)
        if lhs in terminals
            DistTree(DistEnum(lhs))
        elseif max_depth == 0
            DWE(DistTree(DistEnum(X)), flip(true))  # Dummy node, just indicate that there is error
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
    tree.d, observe.d, tree.err
end
bdd = compile(code)
tree_bdd, observe_bdd, error_bdd = bdd
dist = Dict()
error_p = 0.
group_infer(observe_bdd, true, 1.0) do observe, observe_prior, denom
    if !observe return end
    group_infer(error_bdd, observe_prior, denom) do error, prior, p
        if error
            # We don't care about rhs if there is error; normally we would call group_infer again
            global error_p = p/denom
            println(error_p)
        else
            group_infer(tree_bdd, prior, p) do assignment, _, p
                dist[assignment] = p/denom
            end
        end
    end
end
println("Probability of error: $(error_p)")
dist = sort([(join(x, ' '), val) for (x, val) in dist], by= xv -> -xv[2])  # by decreasing probability
print_dict(dist[1:min(length(dist),top_n)])
println("$(num_nodes(bdd)) nodes, $(num_flips(bdd)) flips")

#==
Probability of error: 0.0
Vector{Tuple{String, Float64}} with 2 entries
   S Any[(X, Any[(a, Any[]), (b, Any[]), (Y, Any[(c, Any[])])])] => 0.7777777777777779
   S Any[(Y, Any[(X, Any[(a, Any[])]), (b, Any[]), (c, Any[])])] => 0.22222222222222224
28 nodes, 7 flips
==#