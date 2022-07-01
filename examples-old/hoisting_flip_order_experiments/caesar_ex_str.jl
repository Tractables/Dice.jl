using Revise
using Dice
using Dice: num_flips, num_nodes
include("../util.jl")

function caesar()
    corpus_url = "https://raw.githubusercontent.com/teropa/nlp/master/resources/corpora/gutenberg/shakespeare-macbeth.txt"
    cipher_text = "l"
    corpus = join(c for c in lowercase(read(download(corpus_url), String)) if c in valid_chars)
    counts = Dict([(c, 0) for c in valid_chars])
    for c in corpus
        counts[c] += 1
    end
    valid_char_freqs = [counts[c]/length(corpus) for c in valid_chars]

    caesar_original, caesar_observe = @dice_ite begin
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
            DistString([rotate_char(c, k) for c in s.chars], s.len)
        end

        # Generate cipher text
        k = discrete([1/26 for _ in 0:25])
        # rotateChar(getChar(), DistInt(5))
        chars = [choose_char() for _ in 1:length(cipher_text)]
        original = DistString(chars, DistInt(length(cipher_text)))
        rotated = rotate_str(original, k)
        observe = prob_equals(rotated, cipher_text)
        k, observe
    end
end