using Revise
using Dice
using Plots

f(i, beta) = exp(beta/2^i)/(1 + exp(beta/2^i))

j = 2
beta1 = 0
beta2 = 10
beta3 = 0

a_vec = [flip(f(i, beta1)) for i in 1:j]
a = DistUInt{j}(a_vec)

b_vec = [flip(f(i, beta2)) for i in 1:j]
b = DistUInt{j}(b_vec)

e_vec = [flip(f(i, beta3)) for i in 1:j]
e = DistUInt{j}(b_vec)

c_vec = [flip(f(i, beta1 + beta2)) for i in 1:j]
c = DistUInt{j}(c_vec)

code = @dice begin
            if flip(theta)
                observe(a < b)
            else
                observe(flip(a_lessthan_b))
            end
            # observe(a<b)
            b
end

code = @dice begin
    observe(a<b)
    d = if flip(theta)
        b
    else
        c
    end
    observe(e < d)
    f = if flip(theta2)
        

end

first = pr(code)

a_lessthan_b = pr(a < b)[1]
actual = (exp(beta2)*(beta2 - 1) + 1)/(beta2*(exp(beta2) - 1))
actual = (beta2/(exp(beta2) - 1))*(exp(beta1+beta2)/(beta1 + beta2) - exp(beta2)/beta2 - 1/(beta1 + beta2) + 1/beta2)
theta = a_lessthan_b/actual

discretized_d(x) = exp(beta2*x)*(beta2*x - 1)
(discretized_d(1) - discretized_d(0.75))/(discretized_d(1) - discretized_d(0))
