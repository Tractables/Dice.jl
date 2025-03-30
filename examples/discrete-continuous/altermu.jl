using Pkg; Pkg.activate(@__DIR__)
using Alea, Distributions

precision = 0
DFiP = DistFix{4+precision, precision}
num_pieces = 2
truncation = (-8.0, 8.0)
add_arg = false

data = DFiP.([-2.57251482,  0.33806206,  2.71757796,  1.09861336,  2.85603752,
-0.91651351,  0.15555127, -2.68160347,  2.47043789,  3.47459025,
1.63949862, -1.32148757,  2.64187513,  0.30357848, -4.09546231,
-1.50709863, -0.99517866, -2.0648892 , -2.40317949,  3.46383544,
0.91173696,  1.18222221,  0.04235722, -0.52815171,  1.15551598,
-1.62749724,  0.71473237, -1.08458812,  4.66020296,  1.24563831,
-0.67970862,  0.93461681,  1.18187607, -1.49501051,  2.44755622,
-2.06424237, -0.04584074,  1.93396696,  1.07685273, -0.09837907]);

code = @alea begin
    # TODO use more general `uniform`
    mu1 = bitblast(DFiP, Normal(0, 5), num_pieces, -2.0, 2.0)
    mu2 = bitblast(DFiP, Normal(0, 5), num_pieces, -2.0, 2.0)
    mu3 = bitblast(DFiP, Normal(0, 5), num_pieces, -2.0, 2.0)
    mu = mu1*mu2-mu3
    for datapoint in data
        gaussian_observe(DFiP, num_pieces, truncation[1], truncation[2], mu, 1.0, datapoint, add=add_arg)
    end
    mu1
end;

@time expectation(code)
