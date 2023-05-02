export DistUIntOH, discrete

##################################
# types, structs, and constructors
##################################

"An unsigned random W-bit integer"
struct DistUIntOH{W} <: Dist{Int}
    # first index is most significant bit
    bits::Vector{AnyBool}
    function DistUIntOH{W}(b) where W
        @assert length(b) == W
        new{W}(b)
    end
end

DistUIntOH(bits::AbstractVector) = 
    DistUIntOH{length(bits)}(bits)

function DistUIntOH{W}(i::Int) where W
    @assert i >= 0
    @assert i < W "Int $i cannot be represented as a DistUIntOH{$W}"
    bits = Vector{AnyBool}(undef, W)
    for idx = 1:W
        bits[idx] = ((idx-1) == i)
    end
    DistUIntOH{W}(bits)
end

# const DistUIntOH8 = DistUIntOH{8}

##################################
# inference
##################################

tobits(x::DistUIntOH) = 
    filter(y -> y isa Dist{Bool}, x.bits)

function frombits(x::DistUIntOH{W}, world) where W
    v = 0
    for i = 1:W
        if frombits(x.bits[i], world)
            v += i-1
        end
    end
    v
end

##################################
# methods
##################################

bitwidth(::DistUIntOH{W}) where W = W

function uniform(::Type{DistUIntOH{W}}, n = W) where W
    @assert W >= n >= 0
    return uniform(DistUIntOH{W}, 0, n)
end

function uniform(::Type{DistUIntOH{W}}, start::Int, stop::Int)::DistUIntOH{W} where W
    @assert start >= 0
    @assert stop <= W
    @assert stop > start

    p = 1/(stop-start)
    ps = vcat(zeros(start), fill(p, stop-start), zeros(W-stop))
    discrete(DistUIntOH{W}, ps)
end


function discrete(::Type{DistUIntOH{W}}, p::Vector{Float64}) where W
    @assert sum(p) ≈ 1

    l = length(p)
    p_proxy = vcat(p, zeros(W-l))

    flips = []
    int_vector = []
    cur_z = 1
    for i in 1:W
        f_i = if cur_z <= 0 flip(0) else flip(p_proxy[i]/cur_z > 1 ? 1 : p_proxy[i]/cur_z) end 
        b_i = reduce(&, map(!, flips); init=true) & f_i
        cur_z = cur_z - p_proxy[i]
        push!(flips, f_i)
        push!(int_vector, b_i)
    end 
    if W == 0 DistUIntOH{W}(0) else DistUIntOH{W}(int_vector) end
end

##################################
# casting
##################################

# function Base.convert(x::DistUIntOH{W1}, t::Type{DistUIntOH{W2}}) where W1 where W2
#     if W1 <= W2
#         DistUIntOH{W2}(vcat(fill(false, W2 - W1), x.bits))
#     else
#         err = reduce(&, x.bits[1:W1 - W2])
#         err && error("throwing away bits")
#         DistUIntOH{W2}(x.bits[W1 - W2 + 1:W1])
#     end
# end

# ##################################
# # other method overloading
# ##################################

function prob_equals(x::DistUIntOH{W}, y::DistUIntOH{W}) where W
    mapreduce(prob_equals, &, x.bits, y.bits)
end

function binop_helper(x::DistUIntOH{W}, y::DistUIntOH{W}, op) where W 
    segments = []
    for i in 1:W
        for j in 1:W 
            check = (x.bits[i] & y.bits[j])
            ret = DistUIntOH{W}(op(i-1, j-1))
            push!(segments, (check, ret))
        end 
    end 
    len = length(segments)
    foldr(((x, y), z)->ifelse(x, y, z), segments[1:len-1],init=segments[len][2])   
end 

function Base.isless(x::DistUIntOH{W}, y::DistUIntOH{W}) where W
    conds = []
    for i in 1:W
        before_cond = reduce(|, x.bits[1:i-1], init=false)
        after_cond = reduce(|, y.bits[i:W], init=false)
        push!(conds, before_cond & after_cond)
    end 
    reduce(|, conds)
end


Base.:(<=)(x::DistUIntOH{W}, y::DistUIntOH{W}) where W = !isless(y, x)
Base.:(>=)(x::DistUIntOH{W}, y::DistUIntOH{W}) where W = !isless(x, y)

function Base.:(+)(p1::DistUIntOH{W}, p2::DistUIntOH{W}) where W
    binop_helper(p1, p2, (a,b)->(a+b)%W)
end

function Base.:(-)(p1::DistUIntOH{W}, p2::DistUIntOH{W}) where W
    binop_helper(p1, p2, (a,b)->abs((a-b)%W))
end

function Base.:(*)(p1::DistUIntOH{W}, p2::DistUIntOH{W}) where W
    binop_helper(p1, p2, (a,b)->(a*b)%W)
end 

function Base.:/(p1::DistUIntOH{W}, p2::DistUIntOH{W}) where W #p1/p2
    is_zero = prob_equals(p2, DistUIntOH{W}(0))
    is_zero && error("division by zero")

    function safe_div(a, b)
        if b == 0
            return 0
        end
        return a ÷ b
    end 
    binop_helper(p1, p2, safe_div)
end 

function Base.:%(p1::DistUIntOH{W}, p2::DistUIntOH{W}) where W #p1/p2
    is_zero = prob_equals(p2, DistUIntOH{W}(0))
    is_zero && error("division by zero")

    function safe_mod(a, b)
        if b == 0
            return 0
        end
        return a % b
    end 
    binop_helper(p1, p2, safe_mod)
end 

function Base.ifelse(cond::Dist{Bool}, then::DistUIntOH{W}, elze::DistUIntOH{W}) where W
    (then == elze) && return then
    bits = map(then.bits, elze.bits) do tb, eb
        ifelse(cond, tb, eb)
    end
    DistUIntOH{W}(bits)
end
