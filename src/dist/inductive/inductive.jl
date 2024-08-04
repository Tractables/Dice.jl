# Distributions over inductively-defined types
export @inductive, @match, matches, variants, InductiveType

abstract type InductiveType <: Dist{Any} end

# alternative to `nothing`, so `nothing` can be used as value
_UNSET = gensym("unset")
isunset(x) = x === _UNSET
getunset() = _UNSET

struct DistTaggedUnion <: Dist{Any}
    which::DistUInt32
    dists::Vector
end

function tobits(x::DistTaggedUnion)
    collect(
        Iterators.flatten([
            Iterators.flatten([tobits(d) for d in x.dists if !isunset(d)]),
            tobits(x.which),
        ])
    )
end

function frombits(x::DistTaggedUnion, world)
    which = frombits(x.which, world)
    v = frombits(x.dists[which], world)
    (which, v)
end

function frombits_as_dist(x::DistTaggedUnion, world)
    DistTaggedUnion(
        frombits_as_dist(x.which, world),
        [
            if isunset(dist)
                getunset()
            else
                frombits_as_dist(dist, world)
            end
            for dist in x.dists
        ]
    )
end

function Base.ifelse(cond::Dist{Bool}, then::DistTaggedUnion, elze::DistTaggedUnion)
    dists = [
        if isunset(then_dist)
            elze_dist
        elseif isunset(elze_dist)
            then_dist
        else
            ifelse(cond, then_dist, elze_dist)
        end
        for (then_dist, elze_dist) in zip(then.dists, elze.dists)
    ]
    DistTaggedUnion(ifelse(cond, then.which, elze.which), dists)
end


function Base.match(x::DistTaggedUnion, branches::Vector{Function})
    @assert length(x.dists) == length(branches)
    res = getunset()
    for (i, (dist, f)) in enumerate(zip(x.dists, branches))
        isunset(dist) && continue
        v = f(dist)
        if isunset(res)
            res = v
        else
            res = ifelse(prob_equals(x.which, DistUInt32(i)), v, res)
        end
    end
    res
end

# Note: this requires that the "which" index of both unions are equal
# (Left<Int,Int> 1 != Right<Int,Int> 1)
function prob_equals(x::DistTaggedUnion, y::DistTaggedUnion)
    res = false
    @assert length(x.dists) == length(y.dists)
    for (i, (a, b)) in enumerate(zip(x.dists, y.dists))
        ii = DistUInt32(i)
        res |= !isunset(a) && !isunset(b) && (
            prob_equals(x.which, ii) & prob_equals(y.which, ii) & prob_equals(a, b)
        )
    end
    res
end

function matches end

function variants end

# Usage:
# @inductive Option Some(DistInt32) None()
# @inductive List{T} Nil() Cons(T, List{T})
macro inductive(type, constructors...)
    if length(constructors) == 1 && constructors[1].head == :vect
        constructors = constructors[1].args
    end
    ty = esc(type)
    plist = [
        begin
            @assert constructor.head == :call
            constructor, args... = constructor.args
            constructor => args
        end
        for constructor in constructors
    ]
    tvs = if type isa Expr && type.head == :curly map(esc, type.args[2:end]) else [] end
    quote
        struct $(ty) <: $(esc(:(Dice.InductiveType))) 
            union::$(esc(:(Dice.DistTaggedUnion)))
        end

        dict = Dict(
            $([
                :($(QuoteNode(ctor)) => $(i))
                for (i, (ctor, args)) in enumerate(plist)
            ]...)
        )
        a = [$([
            QuoteNode(ctor) for (ctor, _) in plist
        ]...)]

        function $(esc(:(Base.match)))(x::$(ty), cases) where {$(tvs...)}
            @assert length(cases) == $(length(constructors))
            branches = $(esc(:(Base.Function)))[$([
                :(_ -> error("Constructor $($(QuoteNode(ctor))) missing branch"))
                for (ctor, _) in plist
            ]...)]
            for (ctr, f) in cases
                branches[dict[ctr]] = args -> f(args...)
            end
            $(esc(:(Base.match)))(x.union, branches)
        end

        function $(esc(:(Dice.matches)))(x::$(ty), ctor) where {$(tvs...)}
            prob_equals(x.union.which, DistUInt32(dict[ctor]))
        end

        function $(esc(:(Dice.variants)))(::$(esc(:(Base.Type))){$(ty)}) where {$(tvs...)}
            [$([
                :($(esc(ctor)) => [$(map(esc, args)...)])
                for (ctor, args) in plist
            ]...)]
        end

        function $(esc(:(Dice.ifelse)))(c::$(esc(Dist{Bool})), x::$(ty), y::$(ty)) where {$(tvs...)}
            $(ty)($(esc(:(Base.ifelse)))(c, x.union, y.union))
        end

        function $(esc(:(Dice.prob_equals)))(x::$(ty), y::$(ty)) where {$(tvs...)}
            $(esc(:(Dice.prob_equals)))(x.union, y.union)
        end

        function $(esc(:(Dice.tobits)))(x::$(ty)) where {$(tvs...)}
            $(esc(:(Dice.tobits)))(x.union)
        end

        function $(esc(:(Dice.frombits)))(x::$(ty), world) where {$(tvs...)}
            i, v = $(esc(:(Dice.frombits)))(x.union, world)
            (a[i], v)
        end

        function $(esc(:(Dice.frombits_as_dist)))(x::$(ty), world) where {$(tvs...)}
            $(ty)($(esc(:(Dice.frombits_as_dist)))(x.union, world))
        end

        $([
            begin
                vars = [gensym("$(i)") for i in 1:length(args)]
                vars_annotated = [:($(var)::$(esc(arg))) for (var, arg) in zip(vars, args)]
                tvs_args = [:(::$(esc(:(Base.Type))){$(tv)}) for tv in tvs]
                quote
                    function $(esc(ctor))($(vcat(tvs_args,vars_annotated)...)) where {$(tvs...)}
                        args = Any[$([
                            :($(esc(:(Dice.getunset)))()) for _ in 1:length(constructors)
                        ]...)]
                        args[$(ctor_i)] = [$(vars...)]
                        $(ty)($(esc(:(Dice.DistTaggedUnion)))($(esc(:(Dice.DistUInt32)))($(ctor_i)), args))
                    end
                end
            end
            for (ctor_i, (ctor, args)) in enumerate(plist)
        ]...)
    end
end

macro match(scrutinee, branches)
    @assert branches.head == :vect || branches.head == :tuple
    function branch_to_fn_pair(branch)
        @assert branch.head == :->
        pat, body = branch.args
        @assert pat.head == :call
        ctor, args... = pat.args
        @assert all(isa(x, Symbol) for x in [ctor, args...])
        esc(:(
            $(QuoteNode(ctor)) =>
            ($(args...),) -> $(body)
        ))
    end
    quote
        $(esc(Base.match))($(esc(scrutinee)), [$(
            map(branch_to_fn_pair, branches.args)
        ...)])
    end
end
