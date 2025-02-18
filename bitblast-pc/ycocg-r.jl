
using Dice



DFiP = DistFix{10, 2}

red_vector = Vector(undef, 8)

red = DFiP([uniform(DistFix{8, 0}).mantissa.number.bits..., false, false])
green = DFiP([uniform(DistFix{8, 0}).mantissa.number.bits..., false, false])
blue = DFiP([uniform(DistFix{8, 0}).mantissa.number.bits..., false, false])


