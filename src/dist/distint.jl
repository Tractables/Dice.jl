
export DistInt, uniform, expectation, uniform_arith, uniform_ite, triangle, discrete

##################################
# types, structs, and constructors
##################################

struct DistInt{W} <: Dist{Int}
    # first index is most significant bit
    bits::Vector{AnyBool}
    function DistInt{W}(b) where W
        @assert length(b) == W
        @assert W <= 63
        new{W}(b)
    end
end

DistInt(b) = DistInt{length(b)}(b)

function DistInt{W}(i::Int) where W
    @assert i >= 0
    num_b = ndigits(i, base = 2)
    bits = Vector{AnyBool}(undef, W)
    for bit_idx = W:-1:1
        bits[bit_idx] = (bit_idx > W - num_b) ? Bool(i & 1) : false
        i = i >> 1
    end
    DistInt{W}(bits)
end

##################################
# inference
##################################

tobits(x::DistInt) = 
    filter(y -> y isa Dist{Bool}, x.bits)

function frombits(x::DistInt{W}, world) where W
    v = 0
    for i = 1:W
        if frombits(x.bits[i], world)
            v += 2^(W-i)
        end
    end
    v
end

##################################
# expectation
##################################

function expectation(x::DistInt{W}) where W
    ans = 0
    a = pr(x.bits...)
    start = 2^(W-1)
    for i=1:W
        ans += start*a[i][1]
        start /= 2
    end
    ans
end
    

##################################
# methods
##################################

bitwidth(::DistInt{W}) where W = W

function uniform(::Type{DistInt{W}}, n = W) where W
    @assert W >= n >= 0
    DistInt{W}([i > W-n ? flip(0.5) : false for i=1:W])
end

function uniform_arith(::Type{DistInt{W}}, start::Int, stop::Int)::DistInt{W} where W
    # WARNING: will cause an error in certain cases where overflow is falsely detected
    # instead use with the @dice macro or increase bit-width
    @assert start >= 0
    @assert stop <= 2^W
    @assert stop > start
    if start > 0
        DistInt{W}(start) + uniform_arith(DistInt{W}, 0, stop-start)
    else
        is_power_of_two = (stop) & (stop-1) == 0
        if is_power_of_two
            uniform(DistInt{W}, ndigits(stop, base=2)-1)
        else 
            power_lt = 2^(ndigits(stop, base=2)-1)
            ifelse(flip(power_lt/stop), uniform_arith(DistInt{W}, 0, power_lt), uniform_arith(DistInt{W}, power_lt, stop))
        end
    end
end

function uniform_ite(::Type{DistInt{W}}, start::Int, stop::Int)::DistInt{W} where W
    @assert start >= 0
    @assert stop <= 2^W
    @assert stop > start

    if start == 0
        upper_pow = floor(Int, log2(stop))
        pivots = [0, 2^upper_pow]
        low_pivot = 0
        high_pivot = 2^upper_pow
    else 
        # get our initial powers of two 
        upper_pow = floor(Int, log2(stop))
        lower_pow = ceil(Int, log2(start))
        pivots = [2^p for p=lower_pow:1:upper_pow]
        low_pivot = 2^lower_pow
        high_pivot = 2^upper_pow
    end

    # find remaining pivots
    while low_pivot > start
        new_pivot = low_pivot - 2^floor(Int, log2(low_pivot-start))
        prepend!(pivots, [new_pivot])
        low_pivot = new_pivot
    end
    while high_pivot < stop
        new_pivot = high_pivot + 2^floor(Int, log2(stop-high_pivot))
        append!(pivots, [new_pivot])
        high_pivot = new_pivot
    end
     
    # better way to do this with map?
    segments = []
    total_length = stop-start
    for j=1:1:length(pivots)-1
        a, b = pivots[j], pivots[j+1]
        segment_length = b-a
        segment = uniform_part(DistInt{W}, a, floor(Int, log2(segment_length)))
        prob = flip(segment_length/total_length)
        total_length -= segment_length
        append!(segments, [(prob, segment)])
    end

    len = length(segments)
    foldr(((x, y), z)->ifelse(x, y, z), segments[1:len-1],init=segments[len][2])        
end


function uniform_part(::Type{DistInt{W}}, lower, bit_length) where W 
    bits = Vector{AnyBool}(undef, W)
    num_b = ndigits(lower, base=2)
    for bit_idx = W:-1:1
        bits[bit_idx] = (bit_idx > W - num_b) ? Bool(lower & 1) : false
        lower = lower >> 1
    end

    for bit_idx = W:-1:W-bit_length+1
        bits[bit_idx] = flip(0.5)
    end
    DistInt{W}(bits)
end

# Generates triangle distribution of type t and bits b
function triangle(t::Type{DistInt{W}}, b::Int) where W
    @assert b <= W
    s = false
    n = 2^b
    x = Vector(undef, W)
    y = Vector(undef, W)
    for i = 1:W-b
        x[i] = false
    end
    for i = W - b + 1:W
        x[i] = Dice.ifelse(s, flip(1/2), flip((3n - 2)/ (4n-4)))
        y[i] = flip((n-2)/(3n-2))
        s = s | (x[i] & !y[i])
        n = n/2
    end
    return DistInt{W}(x)
end

# bitwise Holtzen to generate a categorical distribution
function discrete(t::Type{DistInt{W}}, p::Vector{Float64}) where W
    @assert sum(p) ≈ 1

    function recurse(p::Vector, i, s, e, prob::Vector)
        if (i == 0)
            a = sum(prob[s:e])
            if a == 0
                flip(0)
            else
                flip(sum(prob[Int((s+e+1)/2):e])/sum(prob[s:e]))
            end
        else
            (Dice.ifelse(p[length(p) - i + 1], recurse(p, i-1, Int((s+e+1)/2), e, prob), recurse(p, i-1, s, Int((s+e-1)/2), prob)))
        end
    end

    mb = length(p)
    add = W
    p_proxy = vcat(p, zeros(2^add - mb))
    int_vector = []
    for i=1:add
        a = recurse(int_vector, i-1, 1, 2^add, p_proxy)
        push!(int_vector, a)
    end
    if add == 0 DistInt{W}(0) else DistInt{W}(int_vector) end
end

##################################
# casting
##################################

function Base.convert(x::DistInt{W1}, t::Type{DistInt{W2}}) where W1 where W2
    if W1 <= W2
        @show W2
        DistInt{W2}(vcat(fill(false, W2 - W1), x.bits))
    else
        @show W2
        
        err = reduce(&, x.bits[1:W1 - W2])
        err && error("throwing away bits")
        DistInt{W2}(x.bits[W1 - W2 + 1:W1])
    end
end


##################################
# other method overloading
##################################

function prob_equals(x::DistInt{W}, y::DistInt{W}) where W
    mapreduce(prob_equals, &, x.bits, y.bits)
end

function Base.isless(x::DistInt{W}, y::DistInt{W}) where W
    foldr(zip(x.bits,y.bits); init=false) do bits, tail_isless
        xbit, ybit = bits
        (xbit < ybit) | prob_equals(xbit,ybit) & tail_isless
    end
end

function Base.:(+)(x::DistInt{W}, y::DistInt{W}) where W
    z = Vector{AnyBool}(undef, W)
    carry = false
    for i=W:-1:1
        z[i] = xor(x.bits[i], y.bits[i], carry)
        carry = atleast_two(x.bits[i], y.bits[i], carry)
    end
    carry && error("integer overflow")
    DistInt{W}(z)
end

function Base.:(-)(x::DistInt{W}, y::DistInt{W}) where W
    z = Vector{AnyBool}(undef, W)
    borrow = false
    for i=W:-1:1
        z[i] = xor(x.bits[i], y.bits[i], borrow)
        borrow = ifelse(borrow, !x.bits[i] | y.bits[i], !x.bits[i] & y.bits[i])
    end
    borrow && error("integer overflow")
    DistInt{W}(z)
end

function ifelse(cond::Dist{Bool}, then::DistInt{W}, elze::DistInt{W}) where W
    (then == elze) && return then
    bits = map(then.bits, elze.bits) do tb, eb
        ifelse(cond, tb, eb)
    end
    DistInt{W}(bits)
end
  