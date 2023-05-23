using Dice, Distributions 
using Revise
using DelimitedFiles

DFiP = DistFixedPoint{20, 13} # -64 to 64

mu = uniform(DFiP, 0.0, 10.0)
u1 = uniform(DFiP, 0.0, 10.0)
u2 = uniform(DFiP, 0.0, 10.0)

code = @dice begin
            observe(prob_equals(u1 + mu, DFiP(12.0))) 
            observe(prob_equals(u2 + mu, DFiP(8.0)))
            mu
end

a = pr(code)

io = open(string("./bit-latte/gt.txt"), "a")
gt = Vector(undef, 40)
for i = 0:39
    temp = 0
    for j in a
        if (j[1] >= i*0.25) & (j[1] < i*0.25 + 0.25) 
            temp += j[2]
        end
    end
    gt[i+1] = temp
    writedlm(io, [(i)*0.25 temp], ",")
end

close(io)



##########
# mu, u1, u2 = M, U1, U2 
# 2^(6)

# For example, M = 4, U1 = 8, U2 = 4
# p = prob(*mu, u1, u2) == (M, U1, U2))
#  
# 4 <= mu < 4.25
# 8 <= u1 < 8.25
# 4 <= u2  < 4.25
# 12 <= mu + u1 < 12.25
# 8 < mu + u2 < 8.25


# pdf(mu, u1, u2 | mu + u1 = 12, mu + u2 = 8) = pdf(mu, u1, u2, mu + u1 = 12, mu + u2 = 8) / pdf(mu + u1 = 12, mu + u2 = 8)
#                                               
###########
# Ground truth program
#   mu ~ continuous_uniform(0, 10)
#   u1 ~ ...
#   u2 ~ ..
#   observe(u1 + mu = 12.0)
#   observe(u2 + mu = 8.0)
#
#   pr(4< mu < 4.25, 8 < u1 < 8.25, 4 < u2 < 4.25)
#



