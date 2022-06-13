using Dice
using Dice: num_flips, num_nodes
using Revise
include("util.jl")

@enum Symbols ₍ ₎ S X Y a b c
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

expected_sentence = [a, b, c]

start_term = S
num_steps = 4
top_n = 40  # Only the top_n most likely strings are printed

code = @dice begin
    lparen = DistEnum(₍)
    rparen = DistEnum(₎)
    function expand_term(lhs, max_depth)
        if lhs in terminals
            DistVector{DistEnum}(Vector{DistEnum}([DistEnum(lhs)])), flip(false)
        elseif max_depth == 0
            DistVector{DistEnum}(Vector{DistEnum}()), flip(true)
        else
            expansion_error_tups = []
            for (rhs, p) in rules[lhs]
                expansion = DistVector{DistEnum}(Vector{DistEnum}())
                err = flip(false)
                for subterm in rhs
                    x = expand_term(subterm, max_depth - 1)
                    expansion, err = prob_extend(expansion, x[1]), err | x[2] 
                end
                push!(expansion_error_tups, (expansion, err))
            end
            
            # Find flip weights
            v = Vector(undef, length(rules[lhs]))
            s = 1.
            for (i, (rhs, p)) in reverse(collect(enumerate(rules[lhs])))
                v[i] = p/s
                s -= p
            end

            # Choose rhs
            rhs, error = expansion_error_tups[1]
            for i in 2:length(rules[lhs])
                f = flip(v[i])
                rhs = if f expansion_error_tups[i][1] else rhs end
                error = if f expansion_error_tups[i][2] else error end
            end
            if max_depth == num_steps  # Wrapping first iteration w start NT unnecessary
                rhs, error
            else
                rhs_wrapped = prob_extend(DistVector{DistEnum}(Vector{DistEnum}([DistEnum(lhs), DistEnum(₍)])), prob_append(rhs, DistEnum(₎)))
                rhs_wrapped, error
            end
        end
    end
    rhs, error = expand_term(start_term, num_steps)
    rhs_terms = DistVector(Vector{DistEnum}())
    for i = 1:length(rhs.contents)
        is_terminal = false
        for terminal in terminals
            is_terminal |= prob_equals(DistEnum(terminal), rhs.contents[i])
        end
        rhs_terms = if (i - 1 < rhs.len) & is_terminal
            prob_append(rhs_terms, rhs.contents[i])
        else
            rhs_terms
        end
    end
    observe = prob_equals(rhs_terms, DistVector(Vector{DistEnum}([DistEnum(term) for term in expected_sentence])))
    rhs, error, observe
end
bdd = compile(code)
rhs_bdd, error_bdd, observe_bdd = bdd
error_p = 0
dist = Dict()
group_infer(observe_bdd, true, 1.0) do observe, observe_prior, denom
    if !observe return end
    group_infer(error_bdd, observe_prior, denom) do error, prior, p
        if error
            # We don't care about rhs if there is error; normally we would call group_infer again
            global error_p = p/denom
        else
            group_infer(rhs_bdd, prior, p) do assignment, _, p
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
Probability of error: 0
Vector{Tuple{String, Float64}} with 2 entries
   X ₍ a b Y ₍ c ₎ ₎ => 0.7777777777777779
   Y ₍ X ₍ a ₎ b c ₎ => 0.22222222222222224
49 nodes, 7 flips
==#