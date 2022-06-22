import IfElse: ifelse

export Dist, DistBool, prob_equals, infer, ifelse, flip, DistFalse, DistTrue, to_dist, num_nodes

"A probability distribution over values of type `T`"
abstract type Dist{T} end

"The global context of a dice program analysis"
abstract type DiceManager end

to_dist(b::Bool) = DistBool(b)

to_dist(d::Dist) = d

struct DistBool <: Dist{Bool}
    bit
end

DistBool(b::Bool) =
    DistBool(constant(b))

DistFalse() = DistBool(false)

DistTrue() = DistBool(true)

DistBool(p::Number) =
    if iszero(p)
        DistBool(false)
    elseif isone(p)
        DistBool(true)
    else
        DistBool(new_var(p))
    end


infer_bool(x::DistBool; observation::DistBool=DistTrue()) =
    infer_bool((x & observation).bit)/infer_bool(observation.bit)

isliteral(x::DistBool) =
    isliteral(x.bit)

isposliteral(x::DistBool) =
    isposliteral(x.bit)

isnegliteral(x::DistBool) =
    isnegliteral(x.bit)

issat(x::DistBool) =
    issat(x.bit)

isvalid(x::DistBool) =
    isvalid(x.bit)

num_nodes(x; suppress_warning=false) =
    num_nodes(bools(x))

num_nodes(bits::Vector{DistBool}; as_add=true) =  
    num_nodes(map(b -> b.bit, bits); as_add)

num_flips(bits::Vector{DistBool}) =  
    num_vars(map(b -> b.bit, bits))

dump_dot(bits::Vector{DistBool}, filename; as_add=true) =
    dump_dot(map(b -> b.bit, bits), filename; as_add)

flip(p) = DistBool(p)

# display `DistBool` values depending on the manager type
function Base.show(io::IO, x::DistBool) 
    # specific to CuddMgr DistBools...
    print(io, typeof(x))
    show(io, x.bit)
end
    
function biconditional(x::DistBool, y::DistBool)
    DistBool(biconditional(x.bit, y.bit))
end

function Base.:&(x::DistBool, y::DistBool) 
    DistBool(conjoin(x.bit, y.bit))
end 

Base.:&(x::DistBool, y::Bool) = 
    x & DistBool(y)

Base.:&(x::Bool, y::DistBool) = 
    y & x

function Base.:|(x::DistBool, y::DistBool)
    DistBool(disjoin(x.bit, y.bit))
end

Base.:|(x::DistBool, y::Bool) = 
    x | DistBool(y)

Base.:|(x::Bool, y::DistBool) = 
    y | x

negate(x::DistBool) =
    DistBool(negate(x.bit))
    
Base.:!(x::DistBool) = 
    negate(x)

prob_equals(x::DistBool, y::DistBool) =
    biconditional(x,y)

function ifelse(cond::DistBool, then::DistBool, elze::DistBool)
    DistBool(ite(cond.bit, then.bit, elze.bit))
end

ifelse(cond::DistBool, x::Bool, y::DistBool) = 
    ifelse(cond, DistBool(x), y)

ifelse(cond::DistBool, x::DistBool, y::Bool) = 
    ifelse(cond, x, DistBool(y))

ifelse(cond::DistBool, x::Bool, y::Bool) = 
    ifelse(cond, DistBool(x), DistBool(y))

ifelse(cond::DistBool, then::Tuple, elze::Tuple) =
    tuple([ifelse(cond, t, e) for (t, e) in zip(then, elze)]...)

bools(b::DistBool) = [b]

rundice(d::DistBool) =
    rundice(d.bit)