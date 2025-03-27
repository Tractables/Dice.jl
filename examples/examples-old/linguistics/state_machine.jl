using Alea
include("../util.jl")

# See state_machine.jpg for a diagram of this machine
machine = Dict(  # List of transitions
    1 =>  # Start state of edge
        [(2, 'a', .3),  # End state of edge, character, probability of taking
        (2, 'i', .5),
        (1, 't', .2)],
    2 =>
        [(1, 's', .4),
        (3, 'm', .3),
        (4, 'l', .3)],
    3 =>
        [(1, 'o', .5),
        (4, 'e', .5)]
)
acceptors = [4]

# Start state
start = 1

# Maximum number of steps to consider
num_steps = 5

str = DistString(Vector(undef, num_steps), DistInt(num_steps))
state = DistInt(start)
for step_i in 1:num_steps
    c = DistChar(' ')  # Char to add this step (won't update if no available transitions)
    next_state = state  # Next state (won't update if no available transitions)
    # Consider each state we can be at
    for (state1, transitions) in machine
        # Choose next state and char label as if we are at state1
        cand_state, cand_c = discrete(
            ((DistInt(state2), DistChar(char_label)), p)
            for (state2, char_label, p) in transitions
        )

        # Only update if our current state matches state1
        state_matches = prob_equals(state, state1)
        next_state = Alea.ifelse(state_matches, cand_state, next_state)
        c = Alea.ifelse(state_matches, cand_c, c)
    end
    str.chars[step_i] = c
    global state = next_state
end

# Infer with recorded error, which in this case is true in execution paths
# where we fail to reach an accepting state within our steps bound.
reached_accepting_state = reduce(|, [prob_equals(state, DistInt(acceptor)) for acceptor in acceptors])
str_dist, non_accepting_p = infer(str, err=!reached_accepting_state)

println("Probability of not reaching accepting state in $(num_steps) steps: $(non_accepting_p)")
print_dict(str_dist)
println("$(num_nodes([str, reached_accepting_state], suppress_warning=true)) nodes, $(num_flips([str, reached_accepting_state])) flips")

#==
Probability of not reaching accepting state in 5 steps: 0.3769599999999999
   il    => 0.15
   al    => 0.09000000000000001
   ime   => 0.075
   ame   => 0.044999999999999984
   isil  => 0.029999999999999995
   til   => 0.029999999999999995
   asil  => 0.018000000000000002
   isal  => 0.018000000000000002
   tal   => 0.018000000000000002
   time  => 0.014999999999999998
   isime => 0.014999999999999998
   imoil => 0.01125
   asal  => 0.010800000000000002
   asime => 0.009
   isame => 0.008999999999999992
   tame  => 0.008999999999999992
   imoal => 0.006750000000000001
   amoil => 0.006749999999999995
   tisil => 0.005999999999999998
   ttil  => 0.005999999999999998
   ⋮     => ⋮
186 nodes, 22 flips
==#
