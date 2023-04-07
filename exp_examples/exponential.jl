using Revise
using Dice
using Plots

f(i, beta) = exp(beta/2^i)/ (1 + exp(beta/2^i))

# (((flips[i] == 1) ? (alice - 2) : alice) < ((flips[i + N] == 1) ? (bob-2) : bob)) : y[i] ? (1 - y[i])


vec_ans = Vector(undef, 10)

for j in 1:10
    beta1 = -10
    a_vec = [flip(f(i, beta1)) for i in 1:j]
    a = DistUInt{j}(a_vec)

    beta2 = 10
    b_vec = [flip(f(i, beta2)) for i in 1:j]
    b = DistUInt{j}(b_vec)

    code = @dice begin
                observe((a < b) )
                b
                # prob_equals(a, b)
                # (a < b) | prob_equals(a, b)
    end

    vec_ans[j] = expectation(code)/2^j

end



c = pr(prob_equals(a, b))
d = pr(a < b)

c[1]/d[1]

# almost a triangle
function express(beta1, beta2, less_than)
    a_vec = [flip(f(i, beta1)) for i in 1:10]
    a = DistUInt{10}(a_vec)

    b_vec = [flip(f(i, beta2)) for i in 1:10]
    b = DistUInt{10}(b_vec)

    code = @dice begin
                observe(a < b)
                if less_than
                    a
                else
                    b
                end
    end

    p = pr(code)
    return plot(p, title= string(beta1)*", "*string(beta2)*", "*string(less_than))
    # savefig("exponential_plots_"*string(beta1)*"_"*string(beta2)*".png")
end

y = Vector(undef, 9)
z = Vector(undef, 9)
counter = 1
for b1 in [-10, 0, 5]
    for b2 in [-10, 0, 5]
        y[counter] = express(b1, b2, true)
        z[counter] = express(b1, b2, false)
        counter += 1
    end
end

plot(y..., layout = (3, 3), legends = false)
savefig("exponential_true.png")

plot(z..., layout = (3, 3), legends = false)
savefig("exponential_false.png")

express(-10, -5, true)

a_vec = [flip(f(i, -10)) for i in 1:10]
a = DistUInt{10}(a_vec)

b_vec = [flip(f(i, 5)) for i in 1:10]
b = DistUInt{10}(b_vec)

code = @dice begin
            observe(a < b*b)
            a
end

p = pr(code)
plot(p)