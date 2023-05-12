# Extra and experimental Dice.jl features

################################################################################
# More datatypes
################################################################################

# Note that no datatypes are mutable. Each operation returns a modified copy.

# DistChar
# - Wraps a DistUInt
# - The set of valid characters is defined by src/dist/char.jl
# - See test/dist/char_test.jl for example usage

# DistEnum
# - Wraps a DistInt. Its interpretation is determined by some Julia Enum
# - See test/dist/enum_test.jl for example usage

# DistVector
# - A vector with a probabilistic size and contents
# - 1-indexed, like Julia's Vector
# - Getting and setting an element returns a pair whose second element indicates
#   an out-of-bounds error.
# - Get an element with prob_getindex(vec, idx)
# - Set an element with prob_setindex(vec, idx, val)
# - Append with prob_append, concat with prob_extend, check for prefix with
#   prob_startswith.
# - See test/dist/vector_test.jl for example usage


################################################################################
# @dice macro
################################################################################

# The @dice macro supports complicated control flow and imperative observations.
pos = @dice begin
    pos = DistUInt32(1)
    continue_at_each_pos = DistVector([flip(0.01), flip(0.3), true, false])
    while prob_getindex(continue_at_each_pos, pos)
        pos += DistUInt32(1)
    end
    observe(pos > DistUInt32(1))
    pos
end
pr(pos)  # Dict(2 => 0.7, 4 => 0.3)

# An equivalent program without @dice
pos = DistUInt32(1)
continue_at_each_pos = [flip(0.01), flip(0.3), true, false]
still_moving = true
for i in eachindex(continue_at_each_pos)
    pos, still_moving = @dice_ite if still_moving & continue_at_each_pos[i]
        pos + DistUInt32(1), true
    else
        pos, false
    end
end
pr(pos, evidence=pos > DistUInt32(1))  # Dict(2 => 0.7, 4 => 0.3)
