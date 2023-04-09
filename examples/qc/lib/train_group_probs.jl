# Train group_to_psp to such that generate() approximates dataset's distribution
function train_group_probs!(
    cond_bools_to_maximize,
    epochs::Integer=1000,
    learning_rate::AbstractFloat=0.3,
)
    # Compile to BDDs
    bdds_to_maximize, level_to_group = compile_helper(cond_bools_to_maximize, flip_to_group)

    # Learn best flip probs to match dataset
    group_to_psp = copy(group_to_psp)
    for _ in 1:epochs
        group_to_psp = step_flip_probs(group_to_psp, bdds_to_maximize, level_to_group, learning_rate)
    end
    global group_to_psp = group_to_psp
end
