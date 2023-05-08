# Distributions over inductively-defined types

export DistInductive, construct, prob_match, DistInductiveType

abstract type DistInductiveType end

struct DistInductive{T <: DistInductiveType}
    constructor::DistUInt32
    arg_lists::Vector{Union{Vector,Nothing}}
end

function param_lists(::Type{T})::Vector{Pair{String,Vector{Type}}} where T <: DistInductiveType
    error("param_lists not implemented for $(T)")
end

function param_list_dict(t::Type{<:DistInductiveType})
    Dict(
        ctr => (i, params)
        for (i, (ctr, params)) in enumerate(param_lists(t))
    )
end

function tobits(x::DistInductive)
    collect(
        Iterators.flatten([
            Iterators.flatten(
                tobits(y)
                for args in x.arg_lists
                if args !== nothing
                for y in args
            ),
            tobits(x.constructor)
        ])
    )
end

function frombits(x::DistInductive{T}, world) where T
    constructor = frombits(x.constructor, world)
    dist_args = x.arg_lists[constructor]
    @assert dist_args !== nothing
    args = [frombits(arg, world) for arg in dist_args]
    (param_lists(T)[constructor][1], args)
end

function Base.ifelse(cond::Dist{Bool}, then::DistInductive{T}, elze::DistInductive{T}) where T
    arg_lists = [
        if then_args === nothing
            elze_args
        elseif elze_args === nothing
            then_args
        else
            ifelse(cond, then_args, elze_args)
        end
        for (then_args, elze_args) in zip(then.arg_lists, elze.arg_lists)
    ]
    DistInductive{T}(
        ifelse(cond, then.constructor, elze.constructor),
        arg_lists
    )
end


function construct(t::Type{<:DistInductiveType}, constructor::String, args::Vector)
    ctr_i, params = get(param_list_dict(t), constructor) do
        error("$(t) has no constructor $(constructor)")
    end

    @assert length(params) == length(args)
    for (param, arg) in zip(params, args)
        @assert arg isa param "$(t) $(constructor) ctr: expected $(param) got $(arg)"
    end

    arg_lists = Vector{Union{Vector,Nothing}}([nothing for _ in param_lists(t)])
    arg_lists[ctr_i] = args
    DistInductive{t}(DistUInt32(ctr_i), arg_lists)
end

function prob_match(x::DistInductive{T}, cases) where T
    pld = param_list_dict(T)

    branches = Set(map(first, cases))
    branches != keys(pld) && error("branches $(branches) do not match $(typeof(x))'s ctrs")

    res = nothing
    for (ctr, f) in cases
        i, params = pld[ctr]
        args = x.arg_lists[i]
        args === nothing && continue
        v = f(args...)
        if res === nothing
            res = v
        else
            res = ifelse(prob_equals(DistUInt32(i), x.constructor), v, res)
        end
    end
    res
end

function prob_equals(x::DistInductive{T}, y::DistInductive{T}) where T
    res = false
    @assert length(x.arg_lists) == length(y.arg_lists)
    for (i, (x_args, y_args)) in enumerate(zip(x.arg_lists, y.arg_lists))
        if isnothing(x_args) || isnothing(y_args)
            continue
        end
        @assert length(x_args) == length(y_args)
        res |= (
            prob_equals(x.constructor, DistUInt32(i))
            & prob_equals(y.constructor, DistUInt32(i))
            & reduce(&, [prob_equals(xa, ya) for (xa, ya) in zip(x_args, y_args)], init=true)
        )
    end
    res
end
