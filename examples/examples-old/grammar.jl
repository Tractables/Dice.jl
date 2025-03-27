using Alea
using Alea: num_flips, num_nodes
include("util.jl")

@enum Terms S NP VP V Alice Bob and ran saw
rules = [
    (S,  # LHS (always a single nonterminal)
        [([NP, VP], 1.0)]), # Potential RHS, probability
    (NP,
        [([Alice], 0.4),
        ([Bob], 0.4),
        ([NP, and, NP], 0.2)]),
    (VP,
        [([V], 0.7),
        ([V, NP], 0.3)]),
    (V,
        [([ran], 0.4),
        ([saw], 0.6)])
]

start_term = S
num_steps = 4
top_n = 40  # Only the top_n most likely strings are printed

code = @dice_ite begin
    # Level-order traversal of the parse tree
    level = DistVector([DistEnum(start_term)])
    # Each step, we replace all nonterminals to move down a level
    for _ in 1:num_steps
        next_level = DistVector([])
        # For each term in this level of the tree
        for i in 1:length(level.contents)
            in_range = (DistInt(i - 1) < level.len)
            replacement = DistVector([level[i]])
            # Consider each LHS that might match
            for (lhs, rhs_list) in rules
                # Use SBK to choose which RHS to take from this LHS

                # Find flip weights
                v = Vector(undef, length(rhs_list))
                s = 1.
                for (i, (_, p)) in reverse(collect(enumerate(rhs_list)))
                    v[i] = p/s
                    s -= p
                end

                cand_rhs = DistVector([DistEnum(t) for t in rhs_list[1][1]])
                for i in 2:length(rhs_list)
                    (rhs, p) = rhs_list[i]
                    take = flip(v[i])
                    cand_rhs = if take
                        DistVector([DistEnum(t) for t in rhs])
                    else
                        cand_rhs
                    end
                end
    
                # Only replace this term if lhs matches rule
                lhs_match = prob_equals(DistEnum(lhs), level[i])
                replacement = if lhs_match cand_rhs else replacement end
            end
            # Concatenate replacement (if term in range)
            next_level = if in_range prob_extend(next_level, replacement) else next_level end
        end
        level = next_level
    end
    level
end
bdd = compile(code)
@time dist = infer(bdd)
dist = sort([(x, val) for (x, val) in dist], by= xv -> -xv[2])  # by decreasing probability
print_dict(dist[1:min(length(dist),top_n)])
println("$(num_nodes(bdd)) nodes, $(num_flips(bdd)) flips")

#==
  6.496086 seconds (24.26 M allocations: 1.181 GiB, 3.28% gc time, 95.26% compilation time)
Vector{Tuple{Vector{Any}, Float64}} with 40 entries
   Any[Alice, saw]                       => 0.168
   Any[Bob, saw]                         => 0.168
   Any[Bob, ran]                         => 0.11199999999999999 
   Any[Alice, ran]                       => 0.11199999999999999 
   Any[Alice, saw, Alice]                => 0.028800000000000006
   Any[Bob, saw, Bob]                    => 0.028800000000000006
   Any[Bob, saw, Alice]                  => 0.028800000000000006
   Any[Alice, saw, Bob]                  => 0.028800000000000006
   Any[Bob, ran, Bob]                    => 0.0192
   Any[Bob, ran, Alice]                  => 0.0192
   Any[Alice, ran, Bob]                  => 0.0192
   Any[Alice, ran, Alice]                => 0.0192
   Any[Bob, and, Alice, saw]             => 0.013439999999999999
   Any[Bob, and, Bob, saw]               => 0.013439999999999999
   Any[Alice, and, Bob, saw]             => 0.013439999999999999
   Any[Alice, and, Alice, saw]           => 0.013439999999999999
   Any[Bob, and, Bob, ran]               => 0.008959999999999997
   Any[Alice, and, Bob, ran]             => 0.008959999999999997
   Any[Alice, and, Alice, ran]           => 0.008959999999999997
   Any[Bob, and, Alice, ran]             => 0.008959999999999997
   Any[Alice, saw, Alice, and, Alice]    => 0.002304
   Any[Bob, and, Bob, saw, Bob]          => 0.002304
   Any[Alice, and, Bob, saw, Bob]        => 0.002304
   Any[Bob, and, Bob, saw, Alice]        => 0.002304
   Any[Alice, and, Bob, saw, Alice]      => 0.002304
   Any[Alice, saw, Bob, and, Bob]        => 0.002304
   Any[Bob, saw, Bob, and, Alice]        => 0.002304
   Any[Bob, and, Alice, saw, Alice]      => 0.002304
   Any[Bob, saw, Bob, and, Bob]          => 0.002304
   Any[Alice, and, Alice, saw, Alice]    => 0.002304
   Any[Alice, saw, Alice, and, Bob]      => 0.002304
   Any[Bob, and, Alice, saw, Bob]        => 0.002304
   Any[Bob, saw, Alice, and, Bob]        => 0.002304
   Any[Bob, saw, Alice, and, Alice]      => 0.002304
   Any[Alice, and, Alice, saw, Bob]      => 0.002304
   Any[Alice, saw, Bob, and, Alice]      => 0.002304
   Any[Bob, and, Bob, and, Bob, saw]     => 0.0021504
   Any[Bob, and, Alice, and, Bob, saw]   => 0.0021504
   Any[Alice, and, Alice, and, Bob, saw] => 0.0021504
   Any[Bob, and, Alice, and, Alice, saw] => 0.0021504
886 nodes, 23 flips
==#
