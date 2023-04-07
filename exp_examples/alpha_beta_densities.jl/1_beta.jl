using Revise
using Dice
using Plots

f(i, beta) = exp(beta/2^i)/ (1 + exp(beta/2^i))

j = 3
epsilon = 1/(2^j)
beta1 = 0
beta2 = 10

a_vec = [flip(f(i, beta1)) for i in 1:j]
a = DistUInt{j}(a_vec)

b_vec = [flip(f(i, beta2)) for i in 1:j]
b = DistUInt{j}(b_vec)

c_vec = [flip(f(i, beta2)) for i in 1:j] 
c = DistUInt{j}(c_vec)

correction_prob = (exp(beta2*epsilon)*(beta2*epsilon - 1) + 1 ) / beta2^2 
correction_prob2 = (correction_prob * (1 - exp(beta2)))/(1 - exp(beta2*epsilon))
correction_prob3 = correction_prob2*beta2^2/(exp(beta2)*(beta2-1) + 1)
code = @dice begin
            observe(a < b)
            d = if flip(1 - correction_prob3) b else c end
            d
end

eval(x) = exp(beta2*x)*(beta2*x - 1)
ground_truth(x) = (eval(x + epsilon) - eval(x)) / (eval(1) - eval(0))

pr(code)

for i in 0:epsilon:1-epsilon
    @show ground_truth(i)
end

#=
## On unit interval [0, 1]
X ~ 1
Y ~ e^{by}
Z ~ e^{by}
observe(X < Y)
W ~ if flip(t) Z else Y end
return W

t = E^(be)*(be - 1) + 1   X   (1 - E^(b))  X      b^2
    --------------------      -----------       -------------------
        b^2                   (1 - E^(be))      E^(b)*(b - 1) + 1


E^(be)(be + 1) - E^(be)
-----------------------
      -E^(be)

be -> 0 as e -> 0
=#





