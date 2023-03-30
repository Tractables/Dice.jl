# Distributions over inductively-defined types

using Dice
import Dice: frombits, tobits

mutable struct InductiveDistType
    constructors::Vector{Tuple{String, Vector}}
end

InductiveDistType() = InductiveDistType([])

struct DistInductive
    # Julia is not dependently-typed 😢
    type::InductiveDistType
    constructor::DistUInt32
    args_by_constructor::Vector{Union{Tuple,Nothing}}
end

function tobits(x::DistInductive)
    collect(
        Iterators.flatten([
            Iterators.flatten(
                tobits(y)
                for args in x.args_by_constructor
                if args !== nothing
                for y in args
            ),
            tobits(x.constructor)
        ])
    )
end
frombits(::Nothing, _) = nothing

function frombits(x::DistInductive, world)
    constructor = frombits(x.constructor, world)
    dist_args = x.args_by_constructor[constructor]
    args = if dist_args === nothing
        []
    else
        [
            if arg isa DistInductive || true
                frombits(arg, world)
            else
                (frombits(arg, world), [])
            end
            for arg in dist_args
        ]
    end
    (x.type.constructors[constructor][1], args)
end

function Base.ifelse(cond::Dist{Bool}, then::DistInductive, elze::DistInductive)
    @assert then.type == elze.type
    DistInductive(
        then.type,
        ifelse(cond, then.constructor, elze.constructor),
        [
            if then_args === nothing
                elze_args
            elseif elze_args === nothing
                then_args
            else
                ifelse(cond, then_args, elze_args)
            end
            for (then_args, elze_args) in zip(
                then.args_by_constructor,
                elze.args_by_constructor
            )
        ]
    )
end

function construct(t::InductiveDistType, constructor::String, args::Tuple)
    for (i, (c, arg_types)) in enumerate(t.constructors)
        if c == constructor
            @assert length(arg_types) == length(args)
            for (arg, arg_type) in zip(args, arg_types)
                @assert arg isa DistInductive && arg.type == arg_type || arg isa arg_type
            end
            return DistInductive(t, DistUInt32(i), [
                if i == j args else nothing end
                for j in 1:length(t.constructors)
            ])
        end
    end
    error("t has no constructor '$(constructor)'")
end

function match(x::DistInductive, cases)
    # TODO: more flexible argument orders
    res = nothing
    for (i, ((cname, f), (cname2, arg_types), args)) in enumerate(zip(cases, x.type.constructors, x.args_by_constructor))
        @assert cname == cname2
        if args === nothing
            continue
        end
        @assert length(arg_types) == length(args)
        for (arg, arg_type) in zip(args, arg_types)
            @assert arg isa DistInductive && arg.type == arg_type || arg isa arg_type
        end
        v = f(args...)
        if res === nothing
            res = v
        else
            res = ifelse(prob_equals(DistUInt32(i), x.constructor), v, res)
        end
    end
    res
end
