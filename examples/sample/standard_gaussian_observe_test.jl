using Revise
using Dice
using Distributions
using DelimitedFiles

# The density of a normal distribution is as follows:
# 
#   1/√2πσ^2  e^{-(x - μ)^2/2σ^2}
#

naive_observe = Vector(undef, 20)

for i in 1:20
    W = 4 + i
    F = i
    DFiP = DistFix{W, F}
    x = uniform(DFiP, i+4)

    normal = bitblast(DFiP, Normal(0, 1), 8, -8.0, 8.0)

    code = @dice begin 
                    observe(prob_equals(x, normal))
                    x
    end

    naive_observe[i] = num_nodes(allobservations(code))
    io = open("naive_observe.txt", "a")
    writedlm(io, [naive_observe[i]])
    close(io)
end


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

actual_square = Vector(undef, 20)

for i in 1:20
    W = 4 + i
    F = i
    DFiP = DistFix{W, F}
    x = uniform(DFiP, i+4)
    code2 = @dice begin
        squared_x = x*x
        for i in 1:length(squared_x.mantissa.number.bits)
            flip_param = exp(-2.0^(W-F-i-1))
            observe(!squared_x.mantissa.number.bits[i] | (squared_x.mantissa.number.bits[i] & flip(flip_param)))
        end
        x
    end

    actual_square[i] = num_nodes(allobservations(code2))
    io = open("actual_square.txt", "a")
    writedlm(io, [actual_square[i]])
    close(io)
end


square_trick = Vector(undef, 20)

for i in 10:10
    W = 4 + i
    F = i
    DFiP = DistFix{W, F}
    x = uniform(DFiP, i+4)
    code3 = @dice begin
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
                        observe(!squared_x[i, j] | (squared_x[i, j] & flip(flip_param)))
                    end
                end
                x
    end

    dump_dot(allobservations(code3), filename="square_trick.dot")

    square_trick[i] = num_nodes(allobservations(code3))
    io = open("square_trick.txt", "a")
    writedlm(io, [square_trick[i]])
    close(io)

end

using Plots
naive_observe = readdlm("naive_observe.txt")
actual_square = readdlm("actual_square.txt")
square_trick = readdlm("square_trick.txt")
plot(naive_observe, marker=:dot, labels = "prob_equals", xlabel="# bits", ylabel="# BDD Nodes", yaxis=:log, legend=:topleft)
plot!(actual_square, marker=:dot, labels = "x*x")
plot!(square_trick, marker=:dot, labels = "square_matrix")
savefig("square_tricks.png")