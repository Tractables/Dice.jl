using Alea, Distributions
DFiP = DistFix{6, 2}
code = @alea begin
            a = bitblast(DFiP, Normal(0, 1), 4, -8.0, 8.0)
            b = a < DFiP(0.0)
            b
end
@show pr(code)