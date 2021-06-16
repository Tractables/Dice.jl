# probabilistic data types

abstract type ProbData end

num_flips(d::ProbData) = 
    num_flips(d.mgr)

# Booleans

struct ProbBool <: ProbData
    #TODO annotate with pointer type to make isbits?
    mgr
    bit
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

@inline issat(x::ProbBool) =
    issat(x.mgr, x.bit)

@inline isvalid(x::ProbBool) =
    isvalid(x.mgr, x.bit)

@inline bools(b::ProbBool) = [b]

num_nodes(bits::Vector{ProbBool}; as_add=true) =  
    num_nodes(bits[1].mgr, map(b -> b.bit, bits); as_add)

num_nodes(x; as_add=true) =  
    num_nodes(bools(x); as_add)

dump_dot(bits::Vector{ProbBool}, filename; as_add=true) =
    dump_dot(bits[1].mgr, map(b -> b.bit, bits), filename; as_add)

dump_dot(x, filename; as_add=true) =  
    dump_dot(bools(x), filename; as_add)

# Tuples

struct ProbTuple{L <: ProbData, R <: ProbData} <: ProbData
    mgr
    left::L
    right::R
end

prob_equals(x::ProbTuple, ::ProbTuple) = 
    false_constant(x.mgr)

function prob_equals(x::T, y::T) where {T <: ProbTuple}
    left_eq = prob_equals(x.left, y.left)
    # TODO optimize by avoiding unnecessary compilation (false and x)
    # TODO order left and right checks by first fail principle 
    right_eq = prob_equals(x.right, y.right)
    left_eq & right_eq
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

max_bits(i::ProbInt) =
    length(i.bits)

function prob_equals(x::ProbInt, y::ProbInt)
    # TODO optimize by avoiding unnecessary compilation (false and x)
    # TODO order bit checks by first fail principle
    shared = min(max_bits(x), max_bits(y))
    eq = true_constant(x.mgr)
    for i=1:shared
        eq &= prob_equals(x.bits[i], y.bits[i])
    end
    for i=shared+1:max_bits(x)
        eq &= !(x.bits[i])
    end
    for i=shared+1:max_bits(y)
        eq &= !(y.bits[i])
    end
    eq
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
            elseif i> mbelze
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

