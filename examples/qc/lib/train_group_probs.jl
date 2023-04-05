# Train group_to_psp to such that generate() approximates dataset's distribution

function train_group_probs!(
    generate,
    dataset::Vector{<:Dist},
    epochs::Integer,
    learning_rate::AbstractFloat
)
    global flip_to_group
    global group_to_psp
    empty!(flip_to_group)
    empty!(group_to_psp)

    # Use Dice to build computation graph
    generated = generate()
    
    println("Distribution before training:")
    print_dict(pr(generated))
    println()

    # Compile to BDDs
    bools_to_maximize = AnyBool[prob_equals(generated, x) for x in dataset]
    bdds_to_maximize, level_to_group = compile_helper(bools_to_maximize, flip_to_group)

    # Learn best flip probs to match dataset
    group_to_psp = Dict(group => 0. for group in keys(group_to_psp))
    for _ in 1:epochs
        group_to_psp = step_flip_probs(group_to_psp, bdds_to_maximize, level_to_group, learning_rate)
    end

    # Done!
    println("Learned flip probability for each group:")
    print_dict(Dict(group => sigmoid(psp) for (group, psp) in group_to_psp))
    println()

    println("Distribution over lengths after training:")
    print_dict(pr(generate()))
end