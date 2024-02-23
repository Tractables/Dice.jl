using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools
using Plots

bits = 7

n_vec = Vector(undef, 10)
bdd = Vector(undef, 10)
# for n = 1:10
for bits = 1:10
    n = 7
    DFiP = DistFix{2 + bits, bits}

    code = @dice begin
                vec_arg = n_unit_exponentials(DFiP, zeros(n))
                reduce(+, vec_arg)
    end

    @show n, bits, num_nodes(code.returnvalue)
    n_vec[bits] = bits
    bdd[bits] = (num_nodes(code.returnvalue))
end

plot(n_vec, bdd, xlabel = "bits", ylabel = "BDD size")
savefig("bits_bdd.png")
dump_dot(code.returnvalue, filename="unbounded_add.dot")