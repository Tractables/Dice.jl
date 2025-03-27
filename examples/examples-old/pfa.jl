using Alea
using Alea: num_nodes, num_flips
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
num_steps = 15
top_n = 20  # Only the top_n most likely strings are printed

code = @alea_ite begin
    str = Vector(undef, num_steps)
    state = DistInt(start)

    for step_i in 1:num_steps
        c = DistChar(' ')  # Char to add this step (won't update if no available transitions)
        next_state = state  # Next state (won't update if no available transitions)
        # Consider each state we can be at
        for (state1, transitions) in machine
            # Use SBK to choose which transition to take from this state

            # Find flip weights
            v = Vector(undef, length(transitions))
            s = 1.
            for (i, (_, _, p)) in reverse(collect(enumerate(transitions)))
                v[i] = p/s
                s -= p
            end

            # Find next state and char we would append
            cand_state = DistInt(transitions[1][1])
            cand_c = DistChar(transitions[1][2])
            for i in 2:length(transitions)
                (state2, char_label, p) = transitions[i]
                take = flip(v[i])
                cand_state = if take DistInt(state2) else cand_state end
                cand_c = if take DistChar(char_label) else cand_c end
            end

            state_matches = prob_equals(state, state1)
            # Only update if our current state matches state1
            next_state = if state_matches cand_state else next_state end
            c = if state_matches cand_c else c end
        end
        str[step_i] = c
        state = next_state
    end
    [state, str]
end

bdd = compile(code)
@time inference_dict = infer(bdd)

# All the hard work is done, just print inference_dict nicely
non_accepting_p = 0
dist = Dict()
for (state_str, p) in inference_dict
    state, str = state_str[1], strip(join(state_str[2]))
    if state in acceptors
        if !haskey(dist, str)
            dist[str] = 0
        end
        dist[str] += p
    else
        non_accepting_p += p
    end
end

println("Probability of not reaching accepting state in $(num_steps) steps: $(non_accepting_p)")
dist = sort([(x, val) for (x, val) in dist], by= xv -> -xv[2])  # by decreasing probability
print_dict(dist[1:min(length(dist),top_n)])
println("$(num_nodes(bdd)) nodes, $(num_flips(bdd)) flips")

#==
Probability of not reaching accepting state in 15 steps: 0.03753876196560418
Vector{Tuple{SubString{String}, Float64}} with 20 entries
   il     => 0.15
   al     => 0.09000000000000001
   ime    => 0.075
   ame    => 0.045000000000000005
   isil   => 0.029999999999999995
   til    => 0.029999999999999995
   isal   => 0.018000000000000002
   asil   => 0.018000000000000002
   tal    => 0.018000000000000002
   time   => 0.014999999999999998
   isime  => 0.014999999999999998
   imoil  => 0.01125
   asal   => 0.010800000000000002
   tame   => 0.009
   isame  => 0.009
   asime  => 0.009
   imoal  => 0.006750000000000001
   amoil  => 0.006750000000000001
   isisil => 0.005999999999999998
   ttil   => 0.005999999999999998
2841 nodes, 71 flips
==#