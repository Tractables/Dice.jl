# Distributions over inductively-defined types

export InductiveType, DistI, construct, match, matches

abstract type InductiveType end

function param_lists(::Type{T})::Vector{Pair{String,Vector{Type}}} where T <: InductiveType
    error("param_lists not implemented for $(T)")
end

function param_list_dict(T::Type{<:InductiveType})
    Dict(
        ctr => (i, params)
        for (i, (ctr, params)) in enumerate(param_lists(T))
    )
end

struct DistI{T<:InductiveType} <: Dist{Any}
    constructor::DistUInt32
    arg_lists::Vector{Union{Vector,Nothing}}
end


function tobits(x::DistI)
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

function frombits(x::DistI{T}, world) where T
    constructor = frombits(x.constructor, world)
    dist_args = x.arg_lists[constructor]
    @assert dist_args !== nothing
    args = [frombits(arg, world) for arg in dist_args]
    (param_lists(T)[constructor][1], args)
end

function Base.ifelse(cond::Dist{Bool}, then::DistI{T}, elze::DistI{T}) where T
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
    DistI{T}(
        ifelse(cond, then.constructor, elze.constructor),
        arg_lists
    )
end


function construct(t::Type{<:InductiveType}, constructor::String, args::Vector)
    ctr_i, params = get(param_list_dict(t), constructor) do
        error("$(t) has no constructor $(constructor)")
    end

    @assert length(params) == length(args)
    for (param, arg) in zip(params, args)
        @assert arg isa param "$(t) $(constructor) ctr: expected $(param) got $(arg)"
    end

    arg_lists = Vector{Union{Vector,Nothing}}([nothing for _ in param_lists(t)])
    arg_lists[ctr_i] = args
    DistI{t}(DistUInt32(ctr_i), arg_lists)
end

function Base.match(x::DistI{T}, cases) where T
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

function matches(x::DistI{T}, ctr) where T
    pld = param_list_dict(T)
    @assert haskey(pld, ctr)
    match(x, [
        k => (args...) -> k == ctr
        for k in keys(pld)
    ])
end

function prob_equals(x::DistI{T}, y::DistI{T}) where T
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
