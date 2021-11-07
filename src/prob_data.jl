# probabilistic data types
using IfElse: IfElse, ifelse

export ProbData, ProbBool, ProbInt, ProbTuple

abstract type ProbData end

# Booleans

struct ProbBool <: ProbData
    #TODO annotate with pointer type to make isbits?
    mgr
    bit
end

ProbBool(mgr, b::Bool)::ProbBool =
    b ? true_constant(mgr) :  false_constant(mgr)


function Base.show(io::IO, x::ProbBool) 
    if !issat(x)
        print(io, "$(typeof(x))(false)") 
    elseif isvalid(x)
        print(io, "$(typeof(x))(true)")
    elseif isposliteral(x)
        print(io, "$(typeof(x))(f$(firstflip(x)))")
    elseif isnegliteral(x)
        print(io, "$(typeof(x))(-f$(firstflip(x)))")
    else    
        print(io, "$(typeof(x))@$(hash(x.bit)÷ 10000000000000)")
    end
end

@inline false_constant(mgr) =
    ProbBool(mgr, false_node(mgr))

@inline true_constant(mgr) =
    ProbBool(mgr, true_node(mgr))

@inline flip(mgr) =
    ProbBool(mgr, new_var(mgr))
    
@inline biconditional(x::ProbBool, y::ProbBool) =
    ProbBool(x.mgr, biconditional(x.mgr, x.bit, y.bit))

@inline conjoin(x::ProbBool, y::ProbBool) =
    ProbBool(x.mgr, conjoin(x.mgr, x.bit, y.bit))

@inline Base.:&(b::ProbBool, d::ProbBool) = 
    conjoin(b,d)

@inline disjoin(x::ProbBool, y::ProbBool) =
    ProbBool(x.mgr, disjoin(x.mgr, x.bit, y.bit))

@inline Base.:|(b::ProbBool, d::ProbBool) = 
    disjoin(b,d)

@inline prob_equals(x::ProbBool, y::ProbBool) =
    biconditional(x,y)

@inline negate(x::ProbBool) =
    ProbBool(x.mgr, negate(x.mgr, x.bit))
    
@inline Base.:!(b::ProbBool) = 
    negate(b)

@inline ite(cond::ProbBool, then::ProbBool, elze::ProbBool) = 
    ProbBool(cond.mgr, ite(cond.mgr, cond.bit, then.bit, elze.bit))

IfElse.ifelse(condition::ProbBool, x, y) = 
    ite(condition, x, y)

@inline issat(x::ProbBool) =
    issat(x.mgr, x.bit)

@inline isvalid(x::ProbBool) =
    isvalid(x.mgr, x.bit)

@inline isliteral(x::ProbBool) =
    isliteral(x.mgr, x.bit)

@inline isposliteral(x::ProbBool) =
    isposliteral(x.mgr, x.bit)

@inline isnegliteral(x::ProbBool) =
    isnegliteral(x.mgr, x.bit)

@inline firstflip(x::ProbBool) =
    firstvar(x.mgr, x.bit)

@inline bools(b::ProbBool) = [b]

num_nodes(bits::Vector{ProbBool}; as_add=true) =  
    num_nodes(bits[1].mgr, map(b -> b.bit, bits); as_add)

num_nodes(x; as_add=true) =  
    num_nodes(bools(x); as_add)

num_flips(bits::Vector{ProbBool}) =  
    num_vars(bits[1].mgr, map(b -> b.bit, bits))

num_flips(x) =  
    num_flips(bools(x))

dump_dot(bits::Vector{ProbBool}, filename; as_add=true) =
    dump_dot(bits[1].mgr, map(b -> b.bit, bits), filename; as_add)

dump_dot(x, filename; as_add=true) =  
    dump_dot(bools(x), filename; as_add)

# Tuples

struct ProbTuple <: ProbData
    mgr
    left::ProbData
    right::ProbData
end

function prob_equals(x::ProbTuple, y::ProbTuple)
    if typeof(x.left) != typeof(y.left) || typeof(x.right) != typeof(y.right)
        # better to just define equality between different types to be false by default???
        false_constant(x.mgr)
    else
        # TODO order left and right checks by first fail principle 
        left_eq = prob_equals(x.left, y.left)
        if !issat(left_eq)
            false_constant(x.mgr)
        else
            right_eq = prob_equals(x.right, y.right)
            left_eq & right_eq
        end
    end
end

function ite(cond::ProbBool, then::T, elze::T) where {T <: ProbTuple}
    # TODO optimize of deterministic conditions
    left = ite(cond, then.left, elze.left)
    right = ite(cond, then.right, elze.right)
    ProbTuple(cond.mgr, left, right)
end

bools(t::ProbTuple) = [bools(t.left); bools(t.right)]
        
# Integers

struct ProbInt <: ProbData
    mgr
    # first index is least significant bit
    # most significant bits that are always false are trimmed
    bits::Vector{ProbBool}
end

function ProbInt(mgr, i::Int)
    get!(mgr.int_cache, i) do
        @assert i >= 0
        num_b = num_bits(i)
        bits = Vector{ProbBool}(undef, num_b)
        for bit_idx = 1:num_b
            b::Bool = i & 1
            @inbounds bits[bit_idx] = ProbBool(mgr, b) 
            i = i >> 1
        end
        ProbInt(mgr, bits)
    end
end

function ProbInt(bits::Vector)
    ProbInt(bits[1].mgr, bits)
end

max_bits(i::ProbInt) =
    length(i.bits)

@inline flip(mgr, ::Type{ProbInt}, bits::Int) =
    ProbInt(mgr, [flip(mgr) for i = 1:bits])

function prob_equals(x::ProbInt, y::ProbInt)
    cache = x.mgr.equals_cache
    get!(cache, (x.bits, y.bits)) do
        shared = min(max_bits(x), max_bits(y))
        eq = true_constant(x.mgr)
        for i=max_bits(x):-1:shared+1
            eq &= !(x.bits[i])
            !issat(eq) && return eq
        end
        for i=max_bits(y):-1:shared+1
            eq &= !(y.bits[i])
            !issat(eq) && return eq
        end
        for i=shared:-1:1
            eq &= prob_equals(x.bits[i], y.bits[i])
            !issat(eq) && return eq
        end
        eq
    end
end

function ite(cond::ProbBool, then::ProbInt, elze::ProbInt)
    if isvalid(cond)
        then
    elseif !issat(cond)
        elze
    else
        last_sat_bit = 0
        mbthen, mbelze = max_bits(then), max_bits(elze)
        mb = max(mbthen, mbelze)
        z = Vector{ProbBool}(undef, mb)
        for i=1:mb
            z[i] = if i > mbthen 
                !cond & elze.bits[i]
            elseif i > mbelze
                 cond & then.bits[i]
            else
                ite(cond, then.bits[i], elze.bits[i])
            end
            if issat(z[i])
                last_sat_bit = i
            end
        end
        ProbInt(cond.mgr, z[1:last_sat_bit])
    end
end

bools(i::ProbInt) = i.bits

