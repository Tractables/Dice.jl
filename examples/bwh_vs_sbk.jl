using Revise
using Dice
include("util.jl")

# Calculate discrete(0.1, 0.2, 0.3, 0.4) using SBK
sbk = @dice_ite begin
    if flip(1/10)
        DistInt(0)
    elseif flip(2/9)
        DistInt(1)
    elseif flip(3/7)
        DistInt(2)
    else
        DistInt(3)
    end
end

# Calculate discrete(0.1, 0.2, 0.3, 0.4) using BWH
bwh = @dice_ite begin
    b1 = flip(7/10)
    b0 = if b1 flip(4/7) else flip(2/3) end
    DistInt([b0, b1])
end

println("BWH:")
print_dict(infer(bwh))
println()

println("SBK:")
print_dict(infer(sbk))