using Revise
using Dice
using Plots

f(i, beta) = exp(beta/2^i)/ (1 + exp(beta/2^i))

j = 2
beta1 = -10
beta2 = +10

a_vec = [flip(f(i, beta1)) for i in 1:j]
a = DistUInt{j}(a_vec)

b_vec = [flip(f(i, beta2)) for i in 1:j]
b = DistUInt{j}(b_vec)

c = 
c_vec = [flip(f(i, beta1 + beta2)) for i in 1:j] 
c = DistUInt{j}(c_vec)

c = convert(a, DistUInt{j+1}) + convert(b, DistUInt{j+1})
plot(pr(c))

solve(x) = (exp(beta2*x) * (exp(beta2/4) - 1))/(exp(beta2) - 1)
solve(3/4)

code = @dice begin
            (a < b) || flip(0.5438369645366324)
end

code = @dice begin
        if flip((1 - 0.5438369645366324))
            a < b
        else 
            true
        end
end


first = pr(code)
solve(b) = exp(beta1*b + beta2*b)/(beta1*beta1 + beta1*beta2) - exp(beta2*b)/(beta1*beta2) 
ans2 = (solve(1) - solve(0))*beta1 * beta2 /((exp(beta1) - 1)*(exp(beta2) - 1))

code = @dice begin
    observe((a < b) || flip(0.5438369645366324))
    a
end

code = @dice begin
    observe((a < b))
    d = if flip(0.25)
            a
    else 
        c
    end
    d
end


second = pr(code)

solve2(x) = (beta2*x*exp(beta2*x) - exp(beta2*x))/beta2

actual = (solve2(0.5) - solve2(0.25)) / (solve2(1) - solve2(0))

solve3(x) = (beta2/((exp(beta1) - 1)*(exp(beta2) - 1))) * (exp(x*(beta1 + beta2))/(beta1 + beta2) - exp(beta2 * x)/beta2)
actual = (solve3(1) - solve3(0.75) ) / (solve3(1) - solve3(0))

solve4(a) = (1 - a + 1/beta1)*exp(beta1*a)
actual = (solve4(1) - solve4(0.75))/(solve4(1) - solve4(0))

solve5(a) = exp(beta2 + beta1*a)/beta1 - exp(beta1*a + beta2*a)/(beta1 + beta2)
actual = (solve5(0.25) - solve5(0))/(solve5(1) - solve5(0))


a = 