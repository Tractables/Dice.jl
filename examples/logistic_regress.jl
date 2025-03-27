
using Dice

Df = DistFix{17, 2}
xs = [2.0, 3.0]
ys = [1.0, 0.0]

e = [Df(exp(2.0^i)) for i in 3:-1:-2]

function logistic(x::DistFix{W, F}) where {W, F}
    bits = x.mantissa.number.bits
    p = DistFix{17, 2}(0.0)
    for i in 3:-1:-2
        p = p * ifelse(bits[W-F-i], DistFix{17, 2}(exp(2.0^i)), DistFix{17, 2}(1.0))
    end
    p
end

max_denom = exp(3)
theta  = uniform(Df, 0.0, 1.0)
code = @dice begin
            for (x, y) in zip(xs, ys)
                mean = theta * Df(x)
                if y == 1.0
                    for (ix, i) in enumerate(mean.mantissa.number.bits)
                        # @show i, ix
                        if i
                            observe(flip(exp(2.0^(4-ix))/max_denom))
                            # observe(flip(0.5))
                        else
                            observe(flip(1/max_denom))
                        end
                    end
                else
                    for (ix, i) in enumerate(mean.mantissa.number.bits)
                        observe(flip(1/max_denom))
                    end
                end
            end
            theta
end

code = @dice begin
     observe(if !flip(0.5) flip(0.5) else flip(0.4) end)
end

pr(code)

function logistic(x::DistFix{W, F}) where {W, F}
    unif = uniform()
end