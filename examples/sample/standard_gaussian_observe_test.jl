using Dice
using Distributions

# The density of a normal distribution is as follows:
# 
#   1/√2πσ^2  e^{-(x - μ)^2/2σ^2}
#

# function standard_gaussian_observe(x::DistFix{W, F}) where {W, F}

W = 6
F = 2
DFiP = DistFix{W, F}
x = DFiP([false, false, false, flip(0.5), false, false])

normal = bitblast(DFiP, Normal(0, 1), 8, -8.0, 8.0)

code = @dice begin 
                observe(prob_equals(x, normal))
                x
end

pr(code)

function dummy_gauss_observe4(bits)
    @show bits
    for i in 1:length(bits)
        flip_param = exp(-2.0^(W-F-i-1))
        # if bits[i] observe(flip(flip_param)) else true end
        observe(bits[i] && flip(flip_param))
    end
end

code2 = @dice begin

            dummy_gauss_observe4(x.mantissa.number.bits)
            # x
end

pr(code2)

squared_x = x * x
bits = squared_x.mantissa.number.bits
res = true
for (i, j) in enumerate(bits)
    print(i, j)
    @show W-F+i-1
    flip_param = 1/(1 + exp(2^(W-F+i-1)))
    res = res & (prob_equals(j, flip(flip_param)))         
end

pr(res)

W = 5
F = 3
DFiP = DistFix{5, 3}


mu = flip(0.5)
code = @dice begin 
            if mu
                dummy_gauss_observe3(DFiP(1.0).mantissa.number.bits)
            else
                dummy_gauss_observe3(DFiP(1.25).mantissa.number.bits)
            end
        mu
        end
    
pr(code)
