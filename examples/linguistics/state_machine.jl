using Dice
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
num_steps = 10

str = DistString(Vector(undef, num_steps), DistUInt32(num_steps))
state = DistUInt32(start)
for step_i in 1:num_steps
    c = DistChar(' ')  # Char to add this step (won't update if no available transitions)
    next_state = state  # Next state (won't update if no available transitions)
    # Consider each state we can be at
    for (state1, transitions) in machine
        # Choose next state and char label as if we are at state1
        cand_state, cand_c = discrete(
            ((DistUInt32(state2), DistChar(char_label)), p)
            for (state2, char_label, p) in transitions
        )

        # Only update if our current state matches state1
        state_matches = prob_equals(state, DistUInt32(state1))
        next_state = Dice.ifelse(state_matches, cand_state, next_state)
        c = Dice.ifelse(state_matches, cand_c, c)
    end
    str.chars[step_i] = c
    global state = next_state
end

# Infer with recorded error, which in this case is true in execution paths
# where we fail to reach an accepting state within our steps bound.
reached_accepting_state = reduce(|, [prob_equals(state, DistUInt32(acceptor)) for acceptor in acceptors])
str = Dice.ifelse(reached_accepting_state, str, DistString("not accepted"))
str_dist = pr(str)

print_dict(str_dist)

#==
   il           => 0.15
   not accepted => 0.11918356479999997
   al           => 0.09000000000000001
   ime          => 0.075
   ame          => 0.044999999999999984
   til          => 0.029999999999999995
   isil         => 0.029999999999999995
   tal          => 0.018000000000000002
   isal         => 0.018000000000000002
   asil         => 0.018000000000000002
   isime        => 0.014999999999999998
   time         => 0.014999999999999998
   imoil        => 0.01125
   asal         => 0.010800000000000002
   asime        => 0.009
   tame         => 0.008999999999999992
   isame        => 0.008999999999999992
   imoal        => 0.006750000000000001
   amoil        => 0.006749999999999995
   ttil         => 0.005999999999999998
   ⋮            => ⋮
==#
