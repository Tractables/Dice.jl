using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using BenchmarkTools
using DelimitedFiles
using Distributions

function radar_query(p::Int, binbits::Int, shift::Bool)
    code = @dice begin
            t = DistFixParam{binbits + 5, binbits}
            function tri(l::Int, r::Int, t::Type{DistFixParam{T, F}}) where {T, F}
                if flip(2^l/(2^l+2^r)) 
                    anyline(dicecontext(), l, 2^(-2.0*l), t) 
                else 
                    (t(dicecontext(), Float64((2^l + 2^r - 1)/2^F)) - anyline(dicecontext(), r, 2^(-2.0*r), t))[1] 
                end
            end
                
            b1 = flip(0.2)
            b2 = if b1 flip(1) else flip(0.2) end

            x1 = uniform(dicecontext(), 3+binbits, t)
            # x1 = shifted_continuous(dicecontext(), p, t, Uniform(0, 8))
            if shift
                x2 = (shifted_continuous(dicecontext(), p, t, Normal(10, 1.414)) + x1)[1]
            else 
                x2 = (continuous(dicecontext(), p, t, Normal(10, 1.414)) + x1)[1]
            end

            o1 = ((if b1 tri(2+binbits, 0+binbits, t) else tri(2+binbits, 2+binbits, t) end) + x1)[1]
            o2 = ((if b2 tri(2+binbits, 0+binbits, t) else tri(2+binbits, 2+binbits, t) end) + x2)[1]

            obs = flip(1)
            obs &= b1
            Cond(x2, obs)
            # uniform(dicecontext(), 2, DistInt)
            # t(dicecontext(), add_bits(uniform(dicecontext(), 3+binbits, t).number, 1))
            
    end
end

bits = 1
code = radar_query(32, bits, true)
@time expectation(code, :bdd)

code = radar_query(16, bits, false)
@time expectation(code, :bdd) + 1/2^(bits + 1)
variance(code, :bdd)
a = compile(code)
num_nodes(a)
b = infer(code, :bdd)
@time expectation(code, :bdd)
@time expectation(code, :bdd) + 1/2^(bits + 1)
variance(a)