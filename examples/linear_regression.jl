using Dice
using Revise
using Distributions
using Plots


bits = 5
DFiP = DistFix{9+bits, bits}


true_w1 = 0
true_w2 = 2
x1s = Vector(undef, 3)
x2s = Vector(undef, 3)
y1s = Vector(undef, 3)
for i in 1:3
    x1s = rand(Uniform(-2, 2), 3)
    x2s = rand(Uniform(-2, 2), 3)
    error = rand(Normal(0, 1), 3)
    y1s = true_w1.*x1s + true_w2.*x2s + error
end


slab1 = bitblast(DFiP, Normal(0, 1), 64, -8.0, 8.0)
slab2 = bitblast(DFiP, Normal(0, 1), 64, -8.0, 8.0)


plot(pr(slab1))


# theta1 = flip(0.5)
# theta2 = flip(0.5)


# w1 = ifelse(theta1, slab1, DFiP(0.0))
# w2 = ifelse(theta2, slab2, DFiP(2.0))


w1 = slab1
w2 = slab2


error = bitblast(DFiP, Normal(0, 1), 64, -8.0, 8.0)


code = @dice begin
        #    for i in 1:3
        #        observe(prob_equals(DFiP(y1s[i]), DFiP(x1s[i])*w1 + DFiP(x2s[i])*w2 + error) )           
        #    end
        DFiP(x1s[1])*w1
        # w1
end


pr(code, ignore_errors=true)
