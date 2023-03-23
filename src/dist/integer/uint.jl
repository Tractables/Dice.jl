export DistUInt, DistUInt8, DistUInt16, DistUInt32, 
    uniform, uniform_arith, uniform_ite, triangle, discrete

##################################
# types, structs, and constructors
##################################

"An unsigned random W-bit integer"
struct DistUInt{W} <: Dist{Int}
    # first index is most significant bit
    bits::Vector{AnyBool}
    function DistUInt{W}(b) where W
        @assert length(b) == W "Expected $W bits from type but got $(length(b)) bits instead"
        @assert 0 < W <= 63 #julia int overflow messes this up?
        new{W}(b)
    end
end

DistUInt(bits::AbstractVector) = 
    DistUInt{length(bits)}(bits)

function DistUInt{W}(i::Int) where W
    @assert i >= 0
    num_b = ndigits(i, base = 2)
    @assert num_b <= W "Int $i cannot be represented as a DistUInt{$W}"
    bits = Vector{AnyBool}(undef, W)
    for bit_idx = W:-1:1
        bits[bit_idx] = (bit_idx > W - num_b) ? Bool(i & 1) : false
        i = i >> 1
    end
    DistUInt{W}(bits)
end

const DistUInt8 = DistUInt{8}
const DistUInt16 = DistUInt{16}
const DistUInt32= DistUInt{32}


"Construct a uniform random number"
function uniform(::Type{DistUInt{W}}, n = W) where W
    @assert W >= n >= 0
    DistUInt{W}([i > W-n ? flip(0.5) : false for i=1:W])
end

"Construct a uniform random number between `start` (inclusive) and `stop` (exclusive)"
function uniform(::Type{DistUInt{W}}, start, stop; strategy = :arith) where W
    if strategy == :ite 
        uniform_ite(DistUInt{W}, start, stop)
    elseif strategy == :arith
        uniform_arith(DistUInt{W}, start, stop)
    else
        error("Unknown uniform strategy $strategy")
    end
end

"Construct a uniform random number by offsetting a 0-based uniform"
function uniform_arith(::Type{DistUInt{W}}, start, stop) where W
    @assert 0 <= start < stop <= 2^W
    DInt = DistUInt{W}
    if start > 0
        DInt(start) + uniform_arith(DInt, 0, stop-start)
    else
        digits = ndigits(stop, base=2)-1
        pivot = 2^digits
        pivotflip = flip(pivot/stop) # first in variable order
        before = uniform(DInt, digits)
        if pivot == stop
            before
        else 
            after = uniform_arith(DInt, pivot, stop)
            ifelse(pivotflip, before, after)
        end
    end
end

"Construct a uniform random number by case analysis on the bits"
function uniform_ite(::Type{DistUInt{W}}, start::Int, stop::Int)::DistUInt{W} where W
    @assert 0 <= start < stop <= 2^W

    upper_pow = floor(Int, log2(stop))
    high_pivot = 2^upper_pow
    if start == 0
        pivots = [0, 2^upper_pow]
        low_pivot = 0
    else 
        lower_pow = ceil(Int, log2(start))
        pivots = [2^p for p=lower_pow:1:upper_pow]
        low_pivot = 2^lower_pow
    end

    # add remaining pivots
    while low_pivot > start
        new_pivot = low_pivot - 2^floor(Int, log2(low_pivot-start))
        insert!(pivots, 1, new_pivot)
        low_pivot = new_pivot
    end
    while high_pivot < stop
        new_pivot = high_pivot + 2^floor(Int, log2(stop-high_pivot))
        push!(pivots, new_pivot)
        high_pivot = new_pivot
    end
     
    total_length = stop-start
    segments = map(1:length(pivots)-1) do j
        a, b = pivots[j], pivots[j+1]
        segment_length = b-a
        randbits = floor(Int, log2(segment_length))
        segment = DistUInt{W}(a) + uniform(DistUInt{W}, randbits) 
        prob = flip(segment_length/total_length)
        total_length -= segment_length
        (prob, segment)
    end

    foldr( ((x,y),z) -> ifelse(x, y, z), segments[1:end-1], init=segments[end][2])
end

"Construct a triangle distribution with a range of `b` bits"
function triangle(::Type{DistUInt{W}}, b::Int) where W
    @assert b <= W
    s = false
    n = 2^b
    x = Vector(undef, W)
    y = Vector(undef, W)
    for i = 1:W-b
        x[i] = false
    end
    for i = W - b + 1:W
        x[i] = ifelse(s, flip(1/2), flip((3n - 2) / (4n-4)))
        y[i] = flip((n-2)/(3n-2))
        s = s | (x[i] & !y[i])
        n = n/2
    end
    return DistUInt{W}(x)
end

"Construct a categorical distribution from a vector of probabilities `probs` 
(using the bitwise Holtzen encoding strategy)"
function discrete(::Type{DistUInt{W}}, probs) where W
    @assert sum(probs) ≈ 1 "Probabilities $probs do not sum to one ($(sum(probs)))"
    V = ndigits(length(probs)-1; base=2)
    probs = vcat(probs, zeros(2^V - length(probs)))
    bits = []

    function recurse(i, s, e)
        if (i == 0)
            denom = sum(probs[s:e])
            if denom == 0
                false
            else
                flip(sum(probs[Int((s+e+1)/2):e])/denom)
            end
        else
            Dice.ifelse(bits[end-i+1], 
                recurse(i-1, Int((s+e+1)/2), e), 
                recurse(i-1, s, Int((s+e-1)/2)))
        end
    end

    for i=1:V
        a = recurse(i-1, 1, 2^V)
        push!(bits, a)
    end
    x = DistUInt{V}(bits)
    convert(DistUInt{W}, x)
end

function Base.convert(::Type{DistUInt{W2}}, x::DistUInt{W1}) where {W1,W2}
    if W1 <= W2
        DistUInt{W2}(vcat(fill(false, W2 - W1), x.bits))
    else
        err = reduce(&, x.bits[1:W1 - W2])
        err && error("throwing away bits")
        DistUInt{W2}(x.bits[W1 - W2 + 1:W1])
    end
end

##################################
# inference
##################################

tobits(x::DistUInt) = 
    filter(y -> y isa Dist{Bool}, x.bits)

function frombits(x::DistUInt{W}, world) where W
    v = 0
    for i = 1:W
        if frombits(x.bits[i], world)
            v += 2^(W-i)
        end
    end
    v
end

function expectation(x::DistUInt{W}; kwargs...) where W
    ans = 0
    bitprobs = pr(x.bits...; kwargs...)
    start = 2^(W-1)
    for i=1:W
        ans += start * bitprobs[i][true]
        start /= 2
    end
    ans
end

function variance(x::DistUInt{W}; kwargs...) where W
    queries = Vector(undef, Int((W * (W-1))/2))
    counter = 1
    for i = 1:W-1, j = i+1:W
        queries[counter] = x.bits[i] & x.bits[j]
        counter += 1
    end
    prs = pr(x.bits..., queries... ; kwargs...)
    
    probs = Matrix(undef, W, W)
    counter = 1
    for i = 1:W-1
        for j = i+1:W
            probs[i, j] = prs[W + counter][true]
            probs[j, i] = prs[W + counter][true]
            counter += 1
        end
        probs[i, i] = prs[i][true]
    end
    probs[W, W] = prs[W][true]
    
    ans = 0
    exponent1 = 1
    for i = 1:W
        ans += exponent1 * (probs[W+1-i, W+1-i] - probs[W+1-i, W+1-i]^2)
        exponent2 = exponent1*2
        for j = i+1:W
            exponent2 = 2*exponent2
            bi = probs[W+1-i, W+1-i]
            bj = probs[W+1-j, W+1-j]
            bibj = probs[W+1-i, W+1-j]
            ans += exponent2 * (bibj-bi*bj)
        end
        exponent1 = exponent1*4
    end
    return ans
end

##################################
# methods
##################################

bitwidth(::DistUInt{W}) where W = W

function prob_equals(x::DistUInt{W}, y::DistUInt{W}) where W
    mapreduce(prob_equals, &, x.bits, y.bits)
end

function Base.isless(x::DistUInt{W}, y::DistUInt{W}) where W
    foldr(zip(x.bits,y.bits); init=false) do bits, tail_isless
        xbit, ybit = bits
        (xbit < ybit) | prob_equals(xbit,ybit) & tail_isless
    end
end


Base.:(<=)(x::DistUInt{W}, y::DistUInt{W}) where W = !isless(y, x)
Base.:(>=)(x::DistUInt{W}, y::DistUInt{W}) where W = !isless(x, y)

function Base.:(+)(x::DistUInt{W}, y::DistUInt{W}) where W
    z = Vector{AnyBool}(undef, W)
    carry = false
    for i=W:-1:1
        z[i] = xor(x.bits[i], y.bits[i], carry)
        carry = atleast_two(x.bits[i], y.bits[i], carry)
    end
    errorcheck() & carry && error("integer overflow in `+`")
    DistUInt{W}(z)
end

function Base.:(-)(x::DistUInt{W}, y::DistUInt{W}) where W
    z = Vector{AnyBool}(undef, W)
    borrow = false
    for i=W:-1:1
        z[i] = xor(x.bits[i], y.bits[i], borrow)
        borrow = ifelse(borrow, !x.bits[i] | y.bits[i], !x.bits[i] & y.bits[i])
    end
    errorcheck() & borrow && error("integer underflow in `-`")
    DistUInt{W}(z)
end


function Base.:(*)(p1::DistUInt{W}, p2::DistUInt{W}) where W
    P = DistUInt{W}(0)
    shifted_bits = p1.bits
    for i = W:-1:1
        if (i != W)
            shifted_bits = vcat(shifted_bits[2:W], false)
        end
        added = ifelse(p2.bits[i], DistUInt{W}(shifted_bits), DistUInt{W}(0))
        P = P + added
    end
    P
end 

function Base.:/(p1::DistUInt{W}, p2::DistUInt{W}) where W
    errorcheck() & iszero(p2) && error("division by zero")

    ans = Vector(undef, W)
    p1_proxy = DistUInt{W}(0)

    for i = 1:W
        p1_proxy = DistUInt{W}(vcat(p1_proxy.bits[2:W], p1.bits[i]))
        ans[i] = ifelse(p2 > p1_proxy, false, true)
        p1_proxy = @dice_ite if p2 > p1_proxy 
            p1_proxy 
        else 
            # make sure this is guarded (i.e., not using `ifelse``) to avoid underflow
            p1_proxy - p2
        end
    end
    DistUInt{W}(ans)
end 

function Base.:%(p1::DistUInt{W}, p2::DistUInt{W}) where W 
    errorcheck() & iszero(p2) && error("division by zero")

    p1_proxy = DistUInt{W}(0)
    for i = 1:W
        p1_proxy = DistUInt{W}(vcat(p1_proxy.bits[2:W], p1.bits[i]))
        p1_proxy = @dice_ite if p2 > p1_proxy 
            p1_proxy 
        else 
            # make sure this is guarded (i.e., not using `ifelse``) to avoid underflow
            p1_proxy - p2 
        end
    end
    p1_proxy
end 

function Base.:~(x::DistUInt{W}) where W 
    DistUInt{W}(.! x.bits) 
end 

function Base.iszero(x::T) where T <: Dist{Int}
    prob_equals(x, T(0))
end

function Base.ifelse(cond::Dist{Bool}, then::DistUInt{W}, elze::DistUInt{W}) where W
    (then == elze) && return then
    bits = map(then.bits, elze.bits) do tb, eb
        ifelse(cond, tb, eb)
    end
    DistUInt{W}(bits)
end
  