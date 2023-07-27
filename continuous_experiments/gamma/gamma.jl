using Dice
using Plots


# a = flip(0.5)
# for i in 1:1000
#     a = ifelse(a, flip(0.6), flip(0.4))
# end

code = @dice begin
    a = flip(0.5)
    for i in 1:10000
        a = ifelse(a, flip(0.6), flip(0.4))
    end
    ifelse(a, unit_gamma(DistFixedPoint{15, 14}, 1, -7.0), unit_gamma(DistFixedPoint{15, 14}, 1, -1.0))
end

@show expectation(code)
