using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using BenchmarkTools
using DelimitedFiles
using Distributions

code = @dice begin

            function tri(l::Int, r::Int, t::Type{DistFixParam{T, F}}) where {T, F}
                if flip(2^l/(2^l+2^r)) 
                    anyline(dicecontext(), l, 2^(-2.0*l), t) 
                else 
                    (t(dicecontext(), Float64((2^l + 2^r - 1)/2^F)) - anyline(dicecontext(), r, 2^(-2.0*r), t))[1] 
                end
                # (t(dicecontext(), 2^l + 2^r - 1) - triangle(dicecontext(), r, t))[1]
            end
                
    
            b1 = flip(0.2)
            b2 = if b1 flip(1) else flip(0.2) end

            x1 = uniform(dicecontext(), 3+3, DistFixParam{7, 5})
            x2 = (continuous(dicecontext(), 16, DistFixParam{7, 5}, Normal(10, 1.414)) + x1)[1]

            o1 = ((if b1 tri(2+2, 1+2, DistFixParam{7, 5}) else tri(2+2, 2+2, DistFixParam{7, 5}) end) + x1)[1]
            o2 = ((if b2 tri(2+2, 1+2, DistFixParam{7, 5}) else tri(2+2, 2+2, DistFixParam{7, 5}) end) + x2)[1]

            obs = b1
            # Cond(x2, obs)
            continuous(dicecontext(), 16, DistFixParam{10, 5}, Normal(10, 1.414))
            # tri(1+1, 2+1, DistFixParam{7, 1})
            # a = anyline(dicecontext(), 3, 1/64, DistInt)#triangle(dicecontext(), 1, DistInt)
        end

infer(code, :bdd)
a = expectation(code, :bdd)