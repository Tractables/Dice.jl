using Pkg; Pkg.activate(@__DIR__)
using Alea, Distributions

precision = 0
DFiP = DistFix{10+precision, precision}
num_pieces = 2
truncation = (-8.0, 8.0)
add_arg = false

data = DFiP.([1.0, 3.0, 6.0, 10.0, 15.0]);


code = @alea begin
    x = DFiP(0.0)
    v = DFiP(0.0)
    a = DFiP(0.0)
    for datapt in data
        x += v
        v += a
        a += bitblast(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
        o = x + bitblast(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
        observe(o == datapt)
    end
    x
end;

@time expectation(code)