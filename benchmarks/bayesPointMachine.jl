using Pkg; Pkg.activate(@__DIR__)
using Dice, Distributions

precision = 2
DFiP = DistFix{11+precision, precision}
num_pieces = 2
truncation = (-8.0, 8.0)
add_arg = false

data = DFiP.([1.0, 3.0, 6.0, 10.0, 15.0]);

fs1 = DFiP.([63.0,16.0,28.0,55.0,22.0,20.0])
fs2 = DFiP.([38.0,23.0,40.0,27.0,18.0,40.0])
fs3 = DFiP.([1.0,1.0,1.0,1.0,1.0,1.0])
os = [1,0,1,1,0,0]
noise = 0.1

code = @dice begin
    w1 = continuous(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
    w2 = continuous(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
    w3 = continuous(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
    for (f1, f2, f3, o) in zip(fs1, fs2, fs3, os)
        mean = f1*w1 + f2*w2 + f3*w3
        c1 = continuous(DFiP, Normal(0, 0.1), num_pieces, -1.0, 1.0)
        if o == 1
            observe(mean + c1 > DFiP(0.0))
        else
            observe(mean + c1 <= DFiP(0.0))
        end
    end
    w1            
end

@time expectation(code)