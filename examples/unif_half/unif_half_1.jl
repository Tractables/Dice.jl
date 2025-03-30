using Revise
using Alea

bits = 5
t = DistUInt{bits}

u = uniform(t)





function custom_uniform(n::Int)
    # @show n
    binary = digits(n, base=2)
    res = t(0)
    denom = 0
    l = length(binary)
    start = 0

    

    # a = uniform(t, bits)

    flip_vector = Vector(undef, l)

    for i in 1:l
        if binary[i] == 1
            denom = denom + 2^(i-1)
            flip_vector[i] = flip(2^(i-1)/denom)
        end
    end

    a = Vector(undef, bits+1)
    temp = t([flip(0.5) for i in 1:bits])
    for i in 1:bits+1
        if i == 1
            a[i] = uniform(t, i-1)
        else
            a[i] = t(vcat([false for i in i:bits], temp.bits[1:i-1]))
        end
        # a[i] = uniform(t, i-1)
    end




    denom = 0
    for i in 1:l
        if binary[i] == 1
            # @show "yay"
            denom = denom + 2^(i-1)
            # @show i
            # @show 2^(i-1), i, pr(a[i]), 2^(i-1)-1
            res = ifelse(flip(2^(i-1)/denom), a[i] + t(start), res)
            start += 2^(i-1)
        end
    end
    res
end
    



function unif_half1(u::DistUInt{W}) where W
    res = nothing

    for x in 0:2^bits-1
        res = if res === nothing
            uniform(DistUInt{bits}, 0, x+1, strategy=:ite)
        else
            @alea_ite if prob_equals(u, DistUInt{bits}(x))
                # uniform(DistUInt{bits}, 0, x+1, strategy=:ite)
                custom_uniform(x+1)
            else
                res
            end
        end
    end
    res
end

function unif_half2(u::DistUInt{W}) where W
    res = nothing

    for x in 0:2^bits-1
        res = if res === nothing
            uniform(DistUInt{bits}, 0, x+1, strategy=:arith)
        else
            @alea_ite if prob_equals(u, DistUInt{bits}(x))
                uniform(DistUInt{bits}, 0, x+1, strategy=:arith)
                # custom_uniform(x+1)
            else
                res
            end
        end
    end
    res
end

function unif_half3(u::DistUInt{W}) where W
    res = nothing
    a = uniform(t)
    res = a % u
    res
end



res = unif_half1(u)
num_nodes(res)
pr(res)

res = unif_half2(u)
num_nodes(res)
a1 = pr(res)
plot(a1)

res = unif_half3(u)
num_nodes(res)
a2 = pr(res)
plot!(a2)

p = pr(a)

function truncate_to_width(x::DistUInt{W1}, W2) where W1
    DistUInt{W2}(x.bits[W1 - W2 + 1:W1])
end

function rem_trunc(x::DistUInt{W1}, y::DistUInt{W2})::DistUInt{W2} where {W1, W2}
    T = DistUInt{max(W1, W2)}
    res = convert(T, x) % convert(T, y)
    truncate_to_width(res, W2)
end


function unif_half(hi::DistUInt{W})::DistUInt{W} where W
    # note: # could use path cond too
    prod = lcm([BigInt(x) for x in 1:2^bits-1 if x != 0])
    @show prod
    u = uniform(DistUInt{ndigits(prod, base=2)}, 0, prod)
    rem_trunc(u, hi)
end



res = unif_half(u)
num_nodes(res)
a2 = pr(res)
plot!(a2)