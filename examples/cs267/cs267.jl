using Dice

##########################################
# Dice semantics
##########################################

# Flip

code = @dice begin
                a = flip(0.3)
                save_dot(Dice.tobits(a), "./examples/cs267/flip.dot")
                a
end

pr(code)

# Tuple

code = @dice begin
                a = (flip(0.3), flip(0.4))
                save_dot(Dice.tobits(a), "./examples/cs267/tuple.dot")
                a
end
pr(code)

# If-then-else

code = @dice begin
                d = ifelse(flip(0.5), flip(0.4), flip(0.1))
                save_dot([d], "./examples/cs267/ite.dot")
                d
end
pr(code)

# Sequencing

code = @dice begin
    x = flip(0.3)
    y = flip(0.7)
    save_dot([y], "./examples/cs267/let.dot")
    y
end
pr(code)

code = @dice begin
    x = flip(0.3)
    y = ifelse(x, flip(0.3), x)
    save_dot([y], "./examples/cs267/let_adv.dot")
    y
end
pr(code)
