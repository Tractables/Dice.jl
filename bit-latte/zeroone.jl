using Dice, Distributions
using DelimitedFiles
using  JLD
using ThreadTools

# bits = parse(Int64, ARGS[1])
# flag = parse(Int64, ARGS[3])

bits = 8
flag = 1

# p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFixedPoint{8+bits, bits}

ys = [1, -1, 1, -1, -1, -1, 1, 1, 1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1, 1]
xs = DFiP.([6, 8, -1, 0, 5, 1.2, -2, 9.8, 4, 12, 1, 10, 1, 2.2, -6, 9.8, 1, 1, 1, 1])

# t = @timed expectation(@dice begin
#             w1 = uniform(DFiP, -8.0, 8.0)
#             w2 = uniform(DFiP, -8.0, 8.0)

#             for (x, y) in zip(xs, ys)
#                 temp = x*w1 + w2
#                 isneg = temp < DFiP(0.0)
#                 if y == 1
#                     observe(!isneg | (isneg & flip(1/ℯ)))
#                 else
#                     observe(isneg | (!isneg & flip(1/ℯ)))
#                 end
#             end
#             if flag == 1
#                 w1
#             else
#                 w2
#             end
#         end)

# p = t.value


# code = @dice begin
#     w1 = uniform(DFiP, -8.0, 8.0)
#     w2 = uniform(DFiP, -8.0, 8.0)

#     for (x, y) in zip(xs, ys)
#         temp = x*w1 + w2
#         isneg = temp < DFiP(0.0)
#         if y == 1
#             observe(!isneg | (isneg & flip(1/ℯ)))
#         else
#             observe(isneg | (!isneg & flip(1/ℯ)))
#         end
#     end
#     if flag == 1
#         w1
#     else
#         w2
#     end
# end

# a = pr(code)

# include("bit_latte.jl")
# using .BitLatte

# function f(true_y, dir)
#     calibrate(true_y, a, bits, dir)
# end

# n_points = 100
# all_calibrate_pr = @time tmap(f, [Dict("x" => -1, "const" => i) for i in range(-8, 8, n_points)], [string(i) for i in range(1, n_points)])

# save("flag_$flag.jld", "expect", all_calibrate_pr)


# # true_y = Dict("x" => -1, "const" => 1.2)  # for true query
# # # calibrate_pr = calibrate(true_y, boolpr, a, bits)

# # # expectation is also doable


# # println("Before Bit-Latte:")
# # println("Pr(x <= 1.2) = $(boolpr[true])")
# # println("After Bit-Latte:")
# # println("Pr(x <= 1.2) = $(calibrate_pr)")

# flag = 0
# p = pr(@dice uniform(DistUInt{3}))
# DFiP = DistFixedPoint{8+bits, bits}

# t = @timed expectation(@dice begin
#             w1 = uniform(DFiP, -8.0, 8.0)
#             w2 = uniform(DFiP, -8.0, 8.0)

#             for (x, y) in zip(xs, ys)
#                 temp = x*w1 + w2
#                 isneg = temp < DFiP(0.0)
#                 if y == 1
#                     observe(!isneg | (isneg & flip(1/ℯ)))
#                 else
#                     observe(isneg | (!isneg & flip(1/ℯ)))
#                 end
#             end
#             if flag == 1
#                 w1
#             else
#                 w2
#             end
#         end)

# p = t.value

include("bit_latte.jl")
using .BitLatte

n_points = 100

function correction(upper_bound::Float64, dirname::String)
    code = @dice begin
        w1 = uniform(DFiP, -8.0, 8.0)
        w2 = uniform(DFiP, -8.0, 8.0)

        for (x, y) in zip(xs, ys)
            temp = x*w1 + w2
            isneg = temp < DFiP(0.0)
            if y == 1
                observe(!isneg | (isneg & flip(1/ℯ)))
            else
                observe(isneg | (!isneg & flip(1/ℯ)))
            end
        end
        observe(w1 < DFiP(upper_bound) || prob_equals(w1, DFiP(upper_bound)))
        if flag == 1
            w1
        else
            w2
        end
    end

    a = pr(code)

    function f(true_y, dir)
        calibrate(true_y, a, bits, dir)
    end

    # all_calibrate_pr = @time tmap(f, [Dict("x" => -1, "const" => i) for i in range(-8, 8, n_points)], [string(i) for i in range(1, n_points)])

    true_y = Dict("x" => -1, "const" => upper_bound)
    final = f(true_y, dirname)
    final
end

all_calibrate_pr = @time tmap(correction, range(-8, 8, 100), [string(i) for i in range(1, n_points)])

save("flag_$flag.jld", "expect", all_calibrate_pr)
