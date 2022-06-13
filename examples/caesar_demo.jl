using Revise
using Dice
using Dice: num_flips, num_nodes

include("util.jl")

char_freqs = get_char_freqs_from_url("https://raw.githubusercontent.com/teropa/nlp/master/resources/corpora/gutenberg/shakespeare-macbeth.txt")

cipher_text = "lips hgmi!"

function choose_char()
    DistChar(discrete(char_freqs))
end

function rotate_letter(c::DistChar, k::DistInt)
    Dice.ifelse((c < DistChar('a')) | (c > DistChar('z')),
        c,
        begin
            rotated_i = safe_add(c.i, k)
            Dice.ifelse(DistChar(rotated_i) > DistChar('z'),
                DistChar((rotated_i - 26)[1]),
                DistChar(rotated_i))
        end
    )
end

function rotate_str(s::DistString, k::DistInt)
    DistString([rotate_letter(c, k) for c in s.chars], s.len)
end

# Generate cipher text
k = uniform(0:25)
chars = [choose_char() for _ in 1:length(cipher_text)]
original = DistString(chars, DistInt(length(cipher_text)))
rotated = rotate_str(original, k)
observation = prob_equals(rotated, cipher_text)
# hoist!((original, observation))  # hoist with this, sadly it does nothing for this

# Distribution over original strings given observation
dist = @Pr(original | observation)
print_dict(dist)

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
