export DistIntOH, discrete

##################################
# types, structs, and constructors
##################################

"An unsigned random W-bit integer"
struct DistIntOH{S,W} <: Dist{Int}
    # S is start, W is width
    bits::Vector{AnyBool}
    function DistIntOH{S,W}(b) where W where S
        @assert length(b) == W
        new{S,W}(b)
    end
end

DistIntOH(s, bits::AbstractVector) = 
    DistIntOH{s,length(bits)}(bits)

function DistIntOH{S,W}(i::Int) where W where S
    @assert i >= S
    @assert i < S+W "Int $i cannot be represented as a DistIntOH{$S,$W}"
    bits = Vector{AnyBool}(undef, W)
    for idx = 1:W
        bits[idx] = ((idx-1+S) == i)
    end
    DistIntOH{S,W}(bits)
end

# const DistIntOH8 = DistIntOH{8}

##################################
# inference
##################################

tobits(x::DistIntOH) = 
    filter(y -> y isa Dist{Bool}, x.bits)

function frombits(x::DistIntOH{S,W}, world) where W where S
    v = 0
    for i = 1:W
        if frombits(x.bits[i], world)
            v += i-1+S
        end
    end
    v
end

##################################
# methods
##################################

bitwidth(::DistIntOH{S,W}) where W where S = W

function uniform(::Type{DistIntOH{S,W}}, n = W) where W where S
    @assert W >= n >= 0
    return uniform(DistIntOH{S,W}, S, S+n)
end

function uniform(::Type{DistIntOH{S,W}}, start::Int, stop::Int)::DistIntOH{S,W} where W where S
    @assert start >= S
    @assert stop <= S+W
    @assert stop > start

    p = 1/(stop-start)
    ps = vcat(zeros(start-S), fill(p, stop-start), zeros(S+W-stop))
    discrete(DistIntOH{S,W}, ps)
end


function discrete(::Type{DistIntOH{S,W}}, p::Vector{Float64}) where W where S
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
    if W == 0 DistIntOH{S,W}(0) else DistIntOH{S,W}(int_vector) end
end

##################################
# casting
##################################

# function Base.convert(x::DistIntOH{W1}, t::Type{DistIntOH{W2}}) where W1 where W2
#     if W1 <= W2
#         DistIntOH{W2}(vcat(fill(false, W2 - W1), x.bits))
#     else
#         err = reduce(&, x.bits[1:W1 - W2])
#         err && error("throwing away bits")
#         DistIntOH{W2}(x.bits[W1 - W2 + 1:W1])
#     end
# end

# ##################################
# # other method overloading
# ##################################

function prob_equals(x::DistIntOH{S,W}, y::DistIntOH{S,W}) where W where S
    mapreduce(prob_equals, &, x.bits, y.bits)
end

function binop_helper(x::DistIntOH{S,W}, y::DistIntOH{S,W}, op) where W where S
    segments = []
    for i in 1:W
        for j in 1:W
            check = (x.bits[i] & y.bits[j])
            ret = DistIntOH{S,W}(op(i-1+S, j-1+S))
            push!(segments, (check, ret))
        end 
    end 
    len = length(segments)
    foldr(((x, y), z)->ifelse(x, y, z), segments[1:len-1],init=segments[len][2])   
end 

function Base.isless(x::DistIntOH{S,W}, y::DistIntOH{S,W}) where W where S
    conds = []
    for i in 1:W
        before_cond = reduce(|, x.bits[1:i-1], init=false)
        after_cond = reduce(|, y.bits[i:W], init=false)
        push!(conds, before_cond & after_cond)
    end 
    reduce(|, conds)
end


Base.:(<=)(x::DistIntOH{S,W}, y::DistIntOH{S,W}) where W where S = !isless(y, x)
Base.:(>=)(x::DistIntOH{S,W}, y::DistIntOH{S,W}) where W where S = !isless(x, y)


function mod_equiv(s, w, n) 
    k = n % w
    if k < s 
        k + w
    elseif k >= s + w 
        k - w
    else 
        k 
    end 
end 


function Base.:(+)(p1::DistIntOH{S,W}, p2::DistIntOH{S,W}) where W where S
    binop_helper(p1, p2, (a,b)->mod_equiv(S, W, a+b))
end

function Base.:(-)(p1::DistIntOH{S,W}, p2::DistIntOH{S,W}) where W where S
    binop_helper(p1, p2, (a,b)->mod_equiv(S, W, a-b))
end

function Base.:(*)(p1::DistIntOH{S,W}, p2::DistIntOH{S,W}) where W where S
    binop_helper(p1, p2, (a,b)->mod_equiv(S, W, a*b))
end 

function Base.:/(p1::DistIntOH{S,W}, p2::DistIntOH{S,W}) where W where S #p1/p2
    is_zero = prob_equals(p2, DistIntOH{S,W}(0))
    is_zero && error("division by zero")

    function safe_div(a, b)
        if b == 0
            return 0
        end
        return a ÷ b
    end 
    binop_helper(p1, p2, (a, b) -> mod_equiv(S, W, safe_div(a, b)))
end 

function Base.:%(p1::DistIntOH{S,W}, p2::DistIntOH{S,W}) where W where S #p1/p2
    is_zero = prob_equals(p2, DistIntOH{S,W}(0))
    is_zero && error("division by zero")

    function safe_mod(a, b)
        if b == 0
            return 0
        end
        return a % b
    end 
    binop_helper(p1, p2, (a, b) -> mod_equiv(S, W, safe_mod(a, b)))
end 

function Base.ifelse(cond::Dist{Bool}, then::DistIntOH{S,W}, elze::DistIntOH{S,W}) where W where S
    (then == elze) && return then
    bits = map(then.bits, elze.bits) do tb, eb
        ifelse(cond, tb, eb)
    end
    DistIntOH{S,W}(bits)
end
