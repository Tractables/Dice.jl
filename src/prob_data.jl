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

false_constant(mgr) =
    ProbBool(mgr, false_node(mgr))

true_constant(mgr) =
    ProbBool(mgr, true_node(mgr))

flip(mgr) =
    ProbBool(mgr, new_var(mgr))
    
biconditional(x::ProbBool, y::ProbBool) =
    ProbBool(x.mgr, biconditional(x.mgr, x.bit, y.bit))

conjoin(x::ProbBool, y::ProbBool) =
    ProbBool(x.mgr, conjoin(x.mgr, x.bit, y.bit))

Base.:&(b::ProbBool, d::ProbBool) = 
    conjoin(b,d)

disjoin(x::ProbBool, y::ProbBool) =
    ProbBool(x.mgr, disjoin(x.mgr, x.bit, y.bit))

Base.:|(b::ProbBool, d::ProbBool) = 
    disjoin(b,d)

prob_equals(x::ProbBool, y::ProbBool) =
    biconditional(x,y)

negate(x::ProbBool) =
    ProbBool(x.mgr, negate(x.mgr, x.bit))
    
Base.:!(b::ProbBool) = 
    negate(b)

ite(cond::ProbBool, then::ProbBool, elze::ProbBool) = 
    ProbBool(cond.mgr, ite(cond.mgr, cond.bit, then.bit, elze.bit))

issat(x::ProbBool) =
    issat(x.mgr, x.bit)

bools(b::ProbBool) = [b]

num_nodes(bits::Vector{ProbBool}) =  
    num_nodes(bits[1].mgr, map(b -> b.bit, bits))

num_nodes(x) =  
    num_nodes(bools(x))

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
    # index 1 is least significant bit
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
    last_sat_bit = 0
    mbthen, mbelze = max_bits(then), max_bits(elze)
    mb = max(mbthen, mbelze)
    z = Vector{ProbBool}(undef, mb)
    false_bit = false_constant(cond.mgr)
    for i=1:mb
        then_bit = (mbthen >= i) ? then.bits[i] : false_bit
        elze_bit = (mbelze >= i) ? elze.bits[i] : false_bit
        z[i] = ite(cond, then_bit, elze_bit)
        if issat(z[i])
            last_sat_bit = i
        end
    end
    ProbInt(cond.mgr, z[1:last_sat_bit])
end

bools(i::ProbInt) = i.bits

