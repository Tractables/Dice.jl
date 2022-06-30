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

# Start state
start = 1

# Maximum number of steps to consider
num_steps = 5

str = DistString(join('.' for _ in 1:num_steps))
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
        next_state = Dice.ifelse(state_matches, cand_state, next_state)
        c = Dice.ifelse(state_matches, cand_c, c)
    end
    str.chars[step_i] = c
    global state = next_state
end

# mgr, compiler = dist_to_mgr_and_compiler(str)
# inferer = x -> infer_bool(mgr, compiler(x))
# str_dist, non_accepting_p = infer(inferer, str.chars, err=!reached_accepting_state)
# println("Probability of not reaching accepting state in $(num_steps) steps: $(non_accepting_p)")
# print_dict(str_dist)

str_dist = infer(str).dist
# println("Probability of not reaching accepting state in $(num_steps) steps: $(non_accepting_p)")
print_dict(str_dist)
# println()
# d, p = infer(inferer, str.chars[1:8], err=!reached_accepting_state)
# print_dict(d)
println(sum(values(str_dist)))
using Dice
save_cg("cg.jl", str)