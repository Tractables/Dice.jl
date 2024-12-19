using Revise
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
x = uniform(DFiP, 3)

normal = bitblast(DFiP, Normal(0, 1), 8, -8.0, 8.0)

code = @dice begin 
                observe(prob_equals(x, normal))
                x
end

pr(code)
num_nodes(allobservations(code))

function squarex(x::DistFix{W, F}) where {W, F}
    square_coeff = Matrix(undef, W, W)
    for i in 1:W
        for j in 1:W
            if i == j
                square_coeff[i, j] = x.mantissa.number.bits[i]
            elseif j < i
                square_coeff[i, j] = x.mantissa.number.bits[i] & x.mantissa.number.bits[j]
            else
                square_coeff[i, j] = false
            end
        end
    end
    square_coeff
end

code2 = @dice begin
    x = uniform(DFiP, 3)
    squared_x = x*x
    for i in 1:length(squared_x.mantissa.number.bits)
        flip_param = exp(-2.0^(W-F-i-1))
        # flip_param = flip_param/(1+flip_param)
        if squared_x.mantissa.number.bits[i] observe(flip(flip_param)) else true end
        # observe(prob_equals(squared_x.mantissa.number.bits[i], flip(flip_param)))
    end
    x
end

pr(code2)

num_nodes(allobservations(code2))

code3 = @dice begin
            x = uniform(DFiP, 3)
            squared_x = squarex(x)
            for i in 1:W
                for j in 1:i
                    i_hat = 2.0^(W-F-i)
                    j_hat = 2.0^(W-F-j)
                    if i==j
                        flip_param = exp(-i_hat * j_hat/2)
                    else
                        flip_param = exp(-i_hat * j_hat)
                    end
                    # if squared_x[i, j] observe(flip(flip_param)) else true end
                    # squared_x[i, j] && observe(flip(flip_param))
                    observe(!squared_x[i, j] | (squared_x[i, j] & flip(flip_param)))
                end
            end
            x
end

pr(code3)

num_nodes(allobservations(code3))
