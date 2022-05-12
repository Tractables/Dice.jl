using Revise
using Dice
using Dice: num_flips, num_nodes
include("util.jl")

corpus_url = "https://raw.githubusercontent.com/teropa/nlp/master/resources/corpora/gutenberg/shakespeare-macbeth.txt"
cipher_text = "lipps, hmgi!"
corpus = join(c for c in lowercase(read(download(corpus_url), String)) if c in valid_chars)
counts = Dict([(c, 0) for c in valid_chars])
for c in corpus
    counts[c] += 1
end
valid_char_freqs = [counts[c]/length(corpus) for c in valid_chars]

code = @dice begin
    function discrete(p::Vector{Float64})
        mb = length(p)
        v = Vector(undef, mb)
        sum = 1
        for i=1:mb
            v[i] = p[i]/sum
            sum = sum - p[i]
        end
        ans = DistInt(mb-1)
        for i=mb-1:-1:1
            ans = if flip(v[i]) DistInt(i-1) else ans end
        end
        return ans
    end

    function choose_char()
        DistChar(discrete(valid_char_freqs))
    end

    function rotate_char(c::DistChar, k::DistInt)
        if (c < DistChar('a')) | (c > DistChar('z'))
            c
        else
            rotated_i = safe_add(c.i, k)
            if DistChar(rotated_i) > DistChar('z')
                DistChar((rotated_i - 26)[1])
            else
                DistChar(rotated_i)
            end
        end
    end

    function rotate_str(s::DistString, k::DistInt)
        DistString(dicecontext(), [rotate_char(c, k) for c in s.chars], s.len)
    end

    # Generate cipher text
    k = discrete([1/26 for _ in 0:25])
    # rotateChar(getChar(), DistInt(5))
    chars = [choose_char() for _ in 1:length(cipher_text)]
    original = DistString(dicecontext(), chars, DistInt(length(cipher_text)))
    rotated = rotate_str(original, k)
    observe = prob_equals(rotated, cipher_text)
    original, observe
end

# Distribution over original strings given observation
original_bdd, observe_bdd = compile(code)
dist = Dict()
group_infer(observe_bdd, true, 1.0) do observe, observe_prior, denom
    if !observe return end
    group_infer(original_bdd, observe_prior, denom) do assignment, _, p
        dist[assignment] = p/denom
    end
end
dist = sort([(join(x), val) for (x, val) in dist], by= xv -> -xv[2])  # by decreasing probability
print_dict(dist)
println("$(num_nodes([original_bdd, observe_bdd])) nodes")

#==
Vector{Tuple{String, Float64}} with 19 entries
   hello, dice! => 0.951091337390233
   wtaad, sxrt! => 0.019873007213649332       
   khoor, glfh! => 0.019718301779910873       
   lipps, hmgi! => 0.005182780892264721       
   rovvy, nsmo! => 0.0013729082151976914      
   xubbe, tysu! => 0.0008574561999073567      
   dahhk, zeya! => 0.0008150736194574973      
   gdkkn, chbd! => 0.0004604449667917548      
   ebiil, afzb! => 0.0002697464689364389      
   pmttw, lqkm! => 0.0001455626437060041      
   spwwz, otnp! => 8.420989709037785e-5       
   qnuux, mrln! => 7.407027995743526e-5       
   axeeh, wbvx! => 2.5576602286270492e-5      
   byffi, xcwy! => 1.5593127519793324e-5
   uryyb, qvpr! => 7.955707466401379e-6
   zwddg, vauw! => 5.477335391637979e-6
   yvccf, uztv! => 3.9652474428804675e-7
   tqxxa, puoq! => 9.340624632491338e-8
   vszzc, rwqs! => 7.729225526639438e-9
4983 nodes
==#
