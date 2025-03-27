using Alea
using Alea: num_flips, num_nodes
using Revise
include("util.jl")

# ERROR terminal isn't optimal; see grammar_recursive.jl for a better implementation
@enum Terms ran saw Alice Bob and ERROR

num_steps = 4
top_n = 40  # Only the top_n most likely strings are printed

code = @dice_ite begin
    function S(max_depth)
        if max_depth == 0
            DistVector([DistEnum(ERROR)])
        else
            prob_extend(NP(max_depth-1), VP(max_depth-1))
        end
    end
    function NP(max_depth)
        if max_depth == 0
            DistVector([DistEnum(ERROR)])
        elseif flip(4/10)
            DistVector([DistEnum(Alice)])
        elseif flip(4/6)
            DistVector([DistEnum(Bob)])
        else
            prob_extend(
                prob_append(
                    NP(max_depth-1),
                    DistEnum(and)),
                NP(max_depth-1)
            )
        end
    end
    function VP(max_depth)
        if max_depth == 0
            DistVector([DistEnum(ERROR)])
        elseif flip(7/10)
            V(max_depth-1)
        else
            prob_extend(V(max_depth-1), NP(max_depth-1))
        end
    end
    function V(max_depth)
        if max_depth == 0
            DistVector([DistEnum(ERROR)])
        elseif flip(4/10)
            DistVector([DistEnum(ran)])
        else
            DistVector([DistEnum(saw)])
        end
    end
    
    S(num_steps)
end
bdd = compile(code)
@time dist = infer(bdd)
dist = sort([(x, val) for (x, val) in dist], by= xv -> -xv[2])  # by decreasing probability
print_dict(dist[1:min(length(dist),top_n)])
println("$(num_nodes(bdd)) nodes, $(num_flips(bdd)) flips")

#==
Vector{Tuple{Vector{Any}, Float64}} with 40 entries
   Any[Alice, saw]                         => 0.168
   Any[Bob, saw]                           => 0.16799999999999998 
   Any[Bob, ran]                           => 0.11199999999999999 
   Any[Alice, ran]                         => 0.11199999999999996 
   Any[Bob, saw, Bob]                      => 0.028800000000000006
   Any[Alice, saw, Alice]                  => 0.028800000000000006
   Any[Alice, saw, Bob]                    => 0.028800000000000006
   Any[Bob, saw, Alice]                    => 0.028800000000000006
   Any[Bob, ran, Bob]                      => 0.0192
   Any[Alice, ran, Bob]                    => 0.0192
   Any[Alice, ran, Alice]                  => 0.0192
   Any[Bob, ran, Alice]                    => 0.0192
   Any[Bob, and, Bob, saw]                 => 0.013439999999999999
   Any[Bob, and, Alice, saw]               => 0.013439999999999999
   Any[Alice, and, Alice, saw]             => 0.013439999999999999
   Any[Alice, and, Bob, saw]               => 0.013439999999999999
   Any[Bob, and, Alice, ran]               => 0.008959999999999994
   Any[Bob, and, Bob, ran]                 => 0.008959999999999994
   Any[Alice, and, Alice, ran]             => 0.008959999999999994
   Any[Alice, and, Bob, ran]               => 0.008959999999999994
   Any[Alice, saw, Alice, and, Alice]      => 0.0023040000000000022
   Any[Bob, saw, Alice, and, Alice]        => 0.0023040000000000022
   Any[Alice, and, Alice, saw, Alice]      => 0.002304
   Any[Alice, saw, Bob, and, Alice]        => 0.002304
   Any[Bob, and, Bob, saw, Bob]            => 0.002304
   Any[Alice, and, Bob, saw, Alice]        => 0.002304
   Any[Alice, saw, Bob, and, Bob]          => 0.002304
   Any[Bob, saw, Bob, and, Bob]            => 0.002304
   Any[Alice, saw, Alice, and, Bob]        => 0.002304
   Any[Alice, and, Bob, saw, Bob]          => 0.002304
   Any[Bob, saw, Bob, and, Alice]          => 0.002304
   Any[Bob, and, Alice, saw, Bob]          => 0.002304
   Any[Bob, and, Alice, saw, Alice]        => 0.002304
   Any[Bob, saw, Alice, and, Bob]          => 0.002304
   Any[Bob, and, Bob, saw, Alice]          => 0.002304
   Any[Alice, and, Alice, saw, Bob]        => 0.002304
   Any[Alice, and, Bob, and, Bob, saw]     => 0.0021504
   Any[Bob, and, Alice, and, Alice, saw]   => 0.0021504
   Any[Alice, and, Alice, and, Alice, saw] => 0.0021504
   Any[Bob, and, Bob, and, Bob, saw]       => 0.0021504
732 nodes, 23 flips
==#