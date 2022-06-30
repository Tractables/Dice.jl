using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function unemployment(p::Int, binbits::Int)
    code = @dice begin

        # final type that we want
        t = DistSigned{binbits + 5, binbits}

        # type for increasing the precision of gaussian
        t_mp = DistSigned{binbits + 9, binbits + 4}

        # gaussian of type t_mp
        a = continuous(dicecontext(), p, t_mp, Normal(0, 1), 0)

        # uniform of type t
        b = uniform(dicecontext(), 3, t)

        # adding msb's to a for signed integer multiplication
        a = add_bits(a, binbits+5, 0)
        @assert max_bits(a.number) == 2*binbits + 14

        # integer multiplication of a and b
        c = (a.number * b.number)[1]

        # removing the precision and additional higher significant bits
        c = DistSigned{2*binbits + 5, binbits}(c.bits[5:2*binbits + 9])
        
        c

    end
    code
end

f = unemployment(16, 0)
compile(f)
a = infer(f, :bdd)
plot(map(a -> a[1], a), map(a -> a[2], a))
