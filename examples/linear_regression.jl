using Dice
using Revise
using Distributions
using Plots


bits = 5
DFiP = DistFix{9+bits, bits}

nobs = 50

true_w1 = 0
true_w2 = 2

x1s = rand(Uniform(-2, 2), nobs)
x2s = rand(Uniform(-2, 2), nobs)
error = rand(Normal(0, 1), nobs)
y1s = true_w1.*x1s + true_w2.*x2s + error



slab1 = bitblast(DFiP, Normal(0, 2), 64, -8.0, 8.0)
slab2 = bitblast(DFiP, Normal(0, 2), 64, -8.0, 8.0)


# plot(pr(slab1))


# theta1 = flip(0.5)
# theta2 = flip(0.5)


# w1 = ifelse(theta1, slab1, DFiP(0.0))
# w2 = ifelse(theta2, slab2, DFiP(2.0))


w1 = slab1
w2 = slab2


# error = bitblast(DFiP, Normal(0, 2), 64, -8.0, 8.0)


code = @dice begin
           for i in 1:nobs
                error = bitblast(DFiP, Normal(0, 1), 64, -8.0, 8.0)
               observe(prob_equals(DFiP(y1s[i]), DFiP(x1s[i])*w1 + DFiP(x2s[i])*w2 + error) )           
           end
        # DFiP(x1s[1])*w1
        # DFiP(x1s[1])*w1 + DFiP(x2s[1])*w2 + error
        w2
end


p = @timed pr(code, ignore_errors=true)
plot(p)

p = expectation(code, ignore_errors=true)