using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using BenchmarkTools
using DelimitedFiles

function pi_approx(b::Int)
    code = @dice begin
                y = (uniform(dicecontext(), b, DistFixParam{b+1, b}) + DistFixParam{b+1, b}(dicecontext(), 1/2^b))[1]
                x = (uniform(dicecontext(), b, DistFixParam{b+1, b}) + DistFixParam{b+1, b}(dicecontext(), 1/2^b))[1]
                t = round_division(x.number, y.number)
                !t.bits[1]              
    end
    code
end

# function execute()
#     @time infer(pi_approx(17), :bdd)
#     # b = compile(pi(1))
#     # @show num_flips(b)
#     # @show num_nodes(b)
# end

# execute() 

ans1 = Vector{Float64}([(5 - pi)/4, 1 - ((5 - pi)/4)])


io = open("pi_results.txt", "a")

probs = Vector(undef, 20)
kld = Vector{Float64}(undef, 20)
for i = 1:18
    a = infer(pi_approx(i), :bdd)
    probs[i] = a
    kld[i] = kldivergence(ans1, [a, 1-a])
    @show probs[i], kld[i]
    io = open("pi_results.txt", "a")
    writedlm(io, [i probs[i] kld[i]], ",")  
    close(io)
end
close(io)
# readlm(io, ")

@timed infer(pi_approx(5), :bdd)

