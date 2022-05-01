using Dice
using Dice: num_nodes, num_flips
include("util.jl")

machine = Dict([  # List of transitions
    (1,  # Start state of edge
        [(2, 'a', 0.3),  # End state of edge, character, probability of taking
        (2, 'i', 0.5),
        (1, 't', 0.2)]),
    (2,
        [(1, 's', 0.4),
        (3, 'm', 0.3),
        (4, 'l', 0.3)]),
    (3,
        [(1, 'o', 0.5),
        (4, 'e', 0.5)])
])

start = 1
acceptors = [4]
num_steps = 5
top_n = 20  # Only the top_n most likely strings are printed

code = @dice begin
    function state_to_string(state, num_steps)
        if state in acceptors
            DistString(""), flip(false)
        elseif num_steps == 0
            DistString(""), flip(true)
        else
            # Use SBK to choose which transition to take from this state
            transitions = machine[state]

            # Find flip weights
            v = Vector(undef, length(transitions))
            s = 1.
            for (i, (_, _, p)) in reverse(collect(enumerate(transitions)))
                v[i] = p/s
                s -= p
            end

            # Find next state and char we would append
            cand_string, cand_error = state_to_string(transitions[1][1], num_steps-1)
            cand_string = string(transitions[1][2]) + cand_string
            for i in 2:length(transitions)
                (state2, char_label, p) = transitions[i]
                take = flip(v[i])
                str, err = state_to_string(state2, num_steps-1)
                str = string(char_label) + str
                cand_string = if take str else cand_string end
                cand_error = if take err else cand_error end
            end
            cand_string, cand_error
        end
    end
    s, e = state_to_string(start, num_steps)
    [s, e]
end

bdd = compile(code)
error_p = 0
dist = Dict()
group_infer(bdd[2], true, 1.0) do error, prior, p
    if error
        # We don't care about rhs if there is error; normally we would call group_infer again
        global error_p = p 
    else
        group_infer(bdd[1], prior, p) do assignment, _, p
            dist[join(assignment)] = p
        end
    end
end
println("Probability of error: $(error_p)")
dist = sort([(x, val) for (x, val) in dist], by= xv -> -xv[2])  # by decreasing probability
print_dict(dist[1:min(length(dist),top_n)])
println("$(num_nodes(bdd)) nodes, $(num_flips(bdd)) flips")

#==
Probability of error: 0.3769599999999999
Vector{Tuple{String, Float64}} with 20 entries
   il    => 0.15
   al    => 0.09000000000000001
   ime   => 0.075
   ame   => 0.045000000000000005
   isil  => 0.029999999999999995
   til   => 0.029999999999999995
   isal  => 0.018000000000000002
   tal   => 0.018000000000000002
   asil  => 0.018000000000000002
   time  => 0.014999999999999998
   isime => 0.014999999999999998
   imoil => 0.01125
   asal  => 0.010800000000000002
   isame => 0.009
   asime => 0.009
   tame  => 0.009
   amoil => 0.006750000000000001
   imoal => 0.006750000000000001
   tisil => 0.005999999999999998
   ttil  => 0.005999999999999998
1001 nodes, 112 flips
==#