using Alea
using Alea: num_flips, num_nodes
using Revise
include("../util.jl")

@enum Terms ran saw Alice Bob and

function grammar()

    rules = Dict([
        ("S",  # LHS (always a single nonterminal)
            [(["NP", "VP"], 1.0)]), # Potential RHS, probability
        ("NP",
            [([Alice], 0.4),
            ([Bob], 0.4),
            (["NP", and, "NP"], 0.2)]),
        ("VP",
            [(["V"], 0.7),
            (["V", "NP"], 0.3)]),
        ("V",
            [([ran], 0.4),
            ([saw], 0.6)])
    ])

    start_term = "S"
    num_steps = 4
    top_n = 40  # Only the top_n most likely strings are printed

    grammar = @alea_ite begin
        function expand_term(lhs, max_depth)
            if typeof(lhs) == Terms
                DistVector(Vector{DistEnum}([DistEnum(lhs)])), DistBool(false)
            elseif max_depth == 0
                DistVector(Vector{DistEnum}()), flip(true)
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
                rhs, error
            end
        end
        rhs, e = expand_term(start_term, num_steps)
        DWE(rhs, e)
    end
end
# mgr, to_bdd = dist_to_mgr_and_compiler(rhswe)
# inferer = d -> infer_bool(mgr, to_bdd(d))
# dist, error_p = infer(inferer, rhswe)

# println("Probability of error: $(error_p)")
# dist = sort([(x, val) for (x, val) in dist], by= xv -> -xv[2])  # by decreasing probability
# print_dict(dist[1:min(length(dist),top_n)])
# println("$(num_nodes(mgr, map(to_bdd, bools(rhswe)))) nodes")

#==
Probability of error: 0.048763514880000025
Vector{Tuple{Vector{Any}, Float64}} with 40 entries
   Any[Alice, saw]                         => 0.168
   Any[Bob, saw]                           => 0.168
   Any[Alice, ran]                         => 0.11199999999999996
   Any[Bob, ran]                           => 0.11199999999999996
   Any[Bob, saw, Alice]                    => 0.028800000000000006
   Any[Alice, saw, Bob]                    => 0.028800000000000006
   Any[Bob, saw, Bob]                      => 0.028800000000000006
   Any[Alice, saw, Alice]                  => 0.028800000000000006
   Any[Alice, ran, Bob]                    => 0.0192
   Any[Alice, ran, Alice]                  => 0.0192
   Any[Bob, ran, Bob]                      => 0.0192
   Any[Bob, ran, Alice]                    => 0.0192
   Any[Bob, and, Bob, saw]                 => 0.013439999999999999
   Any[Alice, and, Alice, saw]             => 0.013439999999999999
   Any[Bob, and, Alice, saw]               => 0.013439999999999999
   Any[Alice, and, Bob, saw]               => 0.013439999999999999
   Any[Bob, and, Bob, ran]                 => 0.008959999999999994
   Any[Alice, and, Bob, ran]               => 0.008959999999999994
   Any[Bob, and, Alice, ran]               => 0.008959999999999994
   Any[Alice, and, Alice, ran]             => 0.008959999999999994
   Any[Bob, and, Bob, saw, Bob]            => 0.002304
   Any[Alice, and, Alice, saw, Alice]      => 0.002304
   Any[Alice, and, Bob, saw, Alice]        => 0.002304
   Any[Alice, saw, Bob, and, Alice]        => 0.002304
   Any[Bob, saw, Alice, and, Alice]        => 0.002304
   Any[Bob, and, Alice, saw, Alice]        => 0.002304
   Any[Alice, saw, Alice, and, Bob]        => 0.002304
   Any[Alice, and, Bob, saw, Bob]          => 0.002304
   Any[Alice, saw, Alice, and, Alice]      => 0.002304
   Any[Bob, saw, Alice, and, Bob]          => 0.002304
   Any[Bob, saw, Bob, and, Alice]          => 0.002304
   Any[Bob, and, Bob, saw, Alice]          => 0.002304
   Any[Bob, and, Alice, saw, Bob]          => 0.002304
   Any[Alice, saw, Bob, and, Bob]          => 0.002304
   Any[Alice, and, Alice, saw, Bob]        => 0.002304
   Any[Bob, saw, Bob, and, Bob]            => 0.002304
   Any[Alice, and, Alice, and, Alice, saw] => 0.0021504
   Any[Bob, and, Bob, and, Bob, saw]       => 0.0021504
   Any[Alice, and, Alice, and, Bob, saw]   => 0.0021504
   Any[Bob, and, Alice, and, Alice, saw]   => 0.0021504
145 nodes
==#