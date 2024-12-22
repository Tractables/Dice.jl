using Dice


import Dice: tobits, frombits


struct DistFloat <: Dist{Any}
    # value of float is just
    # mantissa * 2^exponent
    exponent::DistInt
    mantissa::DistInt
end
tobits(x::DistFloat) =
    vcat(tobits(x.exponent), tobits(x.mantissa))
frombits(x::DistFloat, world) =
    float(frombits(x.mantissa, world)) * 2^float(frombits(x.exponent, world))
    

var_vals = Valuation()
adnodes_of_interest = Dict{String, ADNode}()
function register_weight!(s)
    var = Var("$(s)_before_sigmoid")
    var_vals[var] = 0
    weight = sigmoid(var)
    adnodes_of_interest[s] = weight
    weight
end

W = 8
function arb_float(s)
    DistFloat(
        DistInt{W}([
            flip(register_weight!("$(s)_exp_$(i)"))
            for i in 1:W
        ]),
        DistInt{W}([
            flip(register_weight!("$(s)_man_$(i)"))
            for i in 1:W
        ]),
    )
end

a = arb_float("a")
b = arb_float("b")
c = arb_float("c")

using Random
Dice.with_concrete_ad_flips(var_vals, (a,b,c)) do
  sample(Random.default_rng(), a)
end

function unstable_