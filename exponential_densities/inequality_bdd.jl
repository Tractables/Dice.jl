using Revise
using Dice

a_vec = Vector(undef, 6)
b_vec = Vector(undef, 6)
for i = 6:-1:4
    a_vec[i] = flip(0.5)
    b_vec[i] = flip(0.5)
end
for i = 3:-1:1
    a_vec[i] = false
    b_vec[i] = false
end
a = DistUInt{6}(a_vec)
b = DistUInt{6}(b_vec)

c = (a < b)
code = @dice begin
            save_dot([c], "inequality_bdd.dot")
            c
end

pr(code)


code = @dice begin
    c = (a + b)
    save_dot(c.bits[4:6], "add_bdd.dot")
    c
end

pr(code)

code = @dice begin
    c = prob_equals(a, b)
    save_dot([c], "equal_bdd.dot")
    c
end

pr(code)


