
export DistSignedInt

##################################
# types, structs, and constructors
##################################

struct DistSignedInt{W} <: Dist{Int}
    number::DistInt{W}
end

function DistSignedInt{W}(b::Vector) where W
    DistSignedInt{W}(DistInt{W}(b))
end

function DistSignedInt{W}(i::Int) where W
    new_i = if i >= 0 i else i + 2^W end
    DistSignedInt{W}(DistInt{W}(new_i))
end

##################################
# inference
##################################

tobits(x::DistSignedInt) = 
    filter(y -> y isa Dist{Bool}, x.number.bits)

function frombits(x::DistSignedInt{W}, world) where W
    v = 0
    if frombits(x.number.bits[1], world)
        v += -2^(W-1)
    end
    for i = 2:W
        if frombits(x.number.bits[i], world)
            v += 2^(W-i)
        end
    end
    v
end

##################################
# expectation
##################################

# function expectation(x::DistInt{W}) where W
#     ans = 0
#     a = pr(x.bits...)
#     start = 2^(W-1)
#     for i=1:W
#         ans += start*a[i][1]
#         start /= 2
#     end
#     ans
# end
    

##################################
# methods
##################################

bitwidth(::DistSignedInt{W}) where W = W

function uniform(::Type{DistSignedInt{W}}, n = W) where W
    DistSignedInt{W}(uniform(DistInt{W}, n).bits)
end

# function uniform_arith(::Type{DistInt{W}}, start::Int, stop::Int)::DistInt{W} where W
#     # WARNING: will cause an error in certain cases where overflow is falsely detected
#     # instead use with the @dice macro or increase bit-width
#     @assert start >= 0
#     @assert stop <= 2^W
#     @assert stop > start
#     if start > 0
#         DistInt{W}(start) + uniform_arith(DistInt{W}, 0, stop-start)
#     else
#         is_power_of_two = (stop) & (stop-1) == 0
#         if is_power_of_two
#             uniform(DistInt{W}, ndigits(stop, base=2)-1)
#         else 
#             power_lt = 2^(ndigits(stop, base=2)-1)
#             ifelse(flip(power_lt/stop), uniform_arith(DistInt{W}, 0, power_lt), uniform_arith(DistInt{W}, power_lt, stop))
#         end
#     end
# end

# function uniform_ite(::Type{DistInt{W}}, start::Int, stop::Int)::DistInt{W} where W
#     @assert start >= 0
#     @assert stop <= 2^W
#     @assert stop > start

#     if start == 0
#         upper_pow = floor(Int, log2(stop))
#         pivots = [0, 2^upper_pow]
#         low_pivot = 0
#         high_pivot = 2^upper_pow
#     else 
#         # get our initial powers of two 
#         upper_pow = floor(Int, log2(stop))
#         lower_pow = ceil(Int, log2(start))
#         pivots = [2^p for p=lower_pow:1:upper_pow]
#         low_pivot = 2^lower_pow
#         high_pivot = 2^upper_pow
#     end

#     # find remaining pivots
#     while low_pivot > start
#         new_pivot = low_pivot - 2^floor(Int, log2(low_pivot-start))
#         prepend!(pivots, [new_pivot])
#         low_pivot = new_pivot
#     end
#     while high_pivot < stop
#         new_pivot = high_pivot + 2^floor(Int, log2(stop-high_pivot))
#         append!(pivots, [new_pivot])
#         high_pivot = new_pivot
#     end
     
#     # better way to do this with map?
#     segments = []
#     total_length = stop-start
#     for j=1:1:length(pivots)-1
#         a, b = pivots[j], pivots[j+1]
#         segment_length = b-a
#         segment = uniform_part(DistInt{W}, a, floor(Int, log2(segment_length)))
#         prob = flip(segment_length/total_length)
#         total_length -= segment_length
#         append!(segments, [(prob, segment)])
#     end

#     len = length(segments)
#     foldr(((x, y), z)->ifelse(x, y, z), segments[1:len-1],init=segments[len][2])        
# end


# function uniform_part(::Type{DistInt{W}}, lower, bit_length) where W 
#     bits = Vector{AnyBool}(undef, W)
#     num_b = ndigits(lower, base=2)
#     for bit_idx = W:-1:1
#         bits[bit_idx] = (bit_idx > W - num_b) ? Bool(lower & 1) : false
#         lower = lower >> 1
#     end

#     for bit_idx = W:-1:W-bit_length+1
#         bits[bit_idx] = flip(0.5)
#     end
#     DistInt{W}(bits)
# end
# ##################################
# # casting
# ##################################

# function Base.convert(x::DistInt{W1}, t::Type{DistInt{W2}}) where W1 where W2
#     if W1 <= W2
#         @show W2
#         DistInt{W2}(vcat(fill(false, W2 - W1), x.bits))
#     else
#         @show W2
        
#         err = reduce(&, x.bits[1:W1 - W2])
#         err && error("throwing away bits")
#         DistInt{W2}(x.bits[W1 - W2 + 1:W1])
#     end
# end


# ##################################
# # other method overloading
# ##################################

function prob_equals(x::DistSignedInt{W}, y::DistSignedInt{W}) where W
    prob_equals(x.number, y.number)
end

# function Base.isless(x::DistInt{W}, y::DistInt{W}) where W
#     foldr(zip(x.bits,y.bits); init=false) do bits, tail_isless
#         xbit, ybit = bits
#         (xbit < ybit) | prob_equals(xbit,ybit) & tail_isless
#     end
# end

# function Base.:(+)(x::DistInt{W}, y::DistInt{W}) where W
#     z = Vector{AnyBool}(undef, W)
#     carry = false
#     for i=W:-1:1
#         z[i] = xor(x.bits[i], y.bits[i], carry)
#         carry = atleast_two(x.bits[i], y.bits[i], carry)
#     end
#     carry && error("integer overflow")
#     DistInt{W}(z)
# end

# function Base.:(-)(x::DistInt{W}, y::DistInt{W}) where W
#     z = Vector{AnyBool}(undef, W)
#     borrow = false
#     for i=W:-1:1
#         z[i] = xor(x.bits[i], y.bits[i], borrow)
#         borrow = ifelse(borrow, !x.bits[i] | y.bits[i], !x.bits[i] & y.bits[i])
#     end
#     borrow && error("integer overflow")
#     DistInt{W}(z)
# end

function ifelse(cond::Dist{Bool}, then::DistSignedInt{W}, elze::DistSignedInt{W}) where W
    DistSignedInt{W}(ifelse(cond, then.number, elze.number))
end
  