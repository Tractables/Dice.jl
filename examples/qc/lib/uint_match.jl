function sticky_sub(x, y)
    @dice_ite if x < y
        DistUInt32(0)
    else
        x - y
    end
end

function Dice.match(x::DistUInt32, branches)
    branch_dict = Dict(branches)
    @dice_ite if prob_equals(x, DistUInt32(0))
        branch_dict["Zero"]()
    else
        branch_dict["Succ"](sticky_sub(x, DistUInt32(1)))
    end
end