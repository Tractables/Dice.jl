using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

bits = 3
# for i = 1:10
    bits = 10
    DFiP = DistFix{2 + bits, bits}

    code = @dice begin
                t(beta, F) = (exp(beta*2.0^(-F))*(beta*2.0^(-F) - 1) + 1)*(1 - exp(beta)) / ((1 - exp(beta*2.0^(-F)))*(exp(beta) * (beta - 1) + 1))

                f1 = flip(t(-2.0, bits))
                f2 = flip(t(-1.0, bits))

                vec_arg = n_unit_exponentials(DFiP, [-2.0, -2.0, 0.0, -1.0, -1.0, 0.0])
                a = unit_gamma(DFiP, 1, -2.0, vec_arg = vec_arg[1:3], coinflips = [f1])
                b = unit_gamma(DFiP, 1, -1.0, vec_arg = vec_arg[4:6], coinflips = [f2])
                a + b
    end

    @show bits, num_nodes(code.returnvalue)
# end

dump_dot(code.returnvalue, filename="add_gamma.dot")