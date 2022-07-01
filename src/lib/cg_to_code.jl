export save_cg

# TODO: have intermediate be a generated Expr instead of writing string to file directly

function save_cg(filename::String, d)
    open(filename, "w") do file
        save_cg(file, d)
    end
end

function save_cg(io::IO, d)
    print(io, "using Dice\n\nfunction cg()\n")

    # Define all flips
    for flip_id in flips_by_instantiation_order(bools(d))
        print(io, "    flip$(flip_id) = flip($(flip_probs[flip_id]))\n")
    end

    # Define all non-constant/flip bools
    next_bool_id = Ref(1)
    cache = IdDict()
    for b in bools(d)
        save_cg_calc_bool(io, b, next_bool_id, cache)
    end

    print(io, "    $(save_cg_to_str(d, cache))\nend\n")
end


function save_cg_calc_bool(io, d::DistBool, next_bool_id, cache)
    (haskey(cache, d) || d isa Union{Flip, DistTrue, DistFalse}) && return
    
    # Calc all prereq bools
    for child in children(d)
        save_cg_calc_bool(io, child, next_bool_id, cache)
    end

    # Print this bool
    print(io, "    b$(next_bool_id[]) = $(save_cg_to_str(d, cache))\n")
    
    # Cache this bool's variable name
    cache[d] = "b$(next_bool_id[])"
    next_bool_id[] += 1
end

save_cg_to_str(::DistTrue, cache) = "DistTrue()"
save_cg_to_str(::DistFalse, cache) = "DistFalse()"
save_cg_to_str(d::Flip, cache) = "flip$(d.id)"

function save_cg_to_str(d::Union{DistAnd, DistOr, DistIte, DistEquals, DistNot}, cache)
    if haskey(cache, d)
        cache[d]
    else
        args = join([save_cg_to_str(child, cache) for child in children(d)], ", ")
        "$(typeof(d))($(args))"
    end
end

function save_cg_to_str(d::DistInt, cache)
    args = join([save_cg_to_str(child, cache) for child in d.bits], ", ")
    "DistInt([$(args)])"
end

function save_cg_to_str(d::DistChar, cache)
    "DistChar($(save_cg_to_str(d.i, cache)))"
end

function save_cg_to_str(d::DistString, cache)
    chars = join([save_cg_to_str(child, cache) for child in d.chars], ", ")
    "DistString([$(chars)], $(save_cg_to_str(d.len, cache)))"
end

function save_cg_to_str(d::Tuple, cache)
    "($(join([save_cg_to_str(x, cache) for x in d], ", ")))"
end

# TODO: support other types. The universal solution might be to first implement
# generic casting between Dist and Vector{DistBool}, as described here:
# https://github.com/Juice-jl/Dice.jl/issues/15
