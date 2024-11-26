using Dice

function linear_regression_bitblast(bits, n, p, X, y)
    DFiP = DistFix{9 + bits, bits}
    pieces = 2^(bits+4)

    ws = [bitblast(DFiP, Normal(0, sqrt(2)), pieces, -16.0, 16.0) for _ in 1:p]
    code = @dice begin
                for i in 1:n
                    error = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
                    linear = reduce(+, map(*, DFiP.(X[i, :]), ws))
                    observe(prob_equals(linear + error, DFiP(y[i])))         
                end
            ws[1]
    end
    expectation(code)
end
