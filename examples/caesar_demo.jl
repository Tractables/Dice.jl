using Dice
using DataStructures: counter

corpus_url = "https://raw.githubusercontent.com/teropa/nlp/master/resources/corpora/gutenberg/shakespeare-macbeth.txt"
cipher_text = "lipps, hmgi!"

function get_char_freqs_from_url(corpus_url)
    corpus = filter(in(valid_chars), lowercase(read(download(corpus_url), String)))
    counts = counter(corpus)
    [counts[c]/length(corpus) for c in valid_chars]
end

function choose_char(char_freqs)
    DistChar(discrete(DistUInt{char_nbits}, char_freqs))
end

function rotate_letter(c::DistChar, k::DistUInt)
    @dice_ite if (c < DistChar('a')) | (c > DistChar('z'))
        c
    else
        rotated_i = c.i + k
        if DistChar(rotated_i) > DistChar('z')
            DistChar(rotated_i - DistUInt{char_nbits}(26))
        else
            DistChar(rotated_i)
        end
    end
end

function rotate_str(s::DistString, k::DistUInt)
    DistString([rotate_letter(c, k) for c in s.chars], s.len)
end

function sample_str(char_freqs, len)
    chars = [choose_char(char_freqs) for _ in 1:len]
    DistString(chars, DistUInt32(len))
end

char_freqs = get_char_freqs_from_url(corpus_url)
original = sample_str(char_freqs, length(cipher_text))
k = uniform(DistUInt{char_nbits}, 0, 25)
rotated = rotate_str(original, k)
dist = pr(original, evidence=prob_equals(rotated, DistString(cipher_text)))
display(dist)

#==
   hello, dice! => 0.9510913373902465
   wtaad, sxrt! => 0.01987300721364919
   khoor, glfh! => 0.019718301779911154
   lipps, hmgi! => 0.005182780892264758
   rovvy, nsmo! => 0.0013729082151976621
   xubbe, tysu! => 0.0008574561999073567
   dahhk, zeya! => 0.0008150736194575031
   gdkkn, chbd! => 0.0004604449667917581
   ebiil, afzb! => 0.00026974646893644275
   pmttw, lqkm! => 0.00014556264370600515
   spwwz, otnp! => 8.420989709037786e-5
   qnuux, mrln! => 7.407027995743422e-5
   axeeh, wbvx! => 2.5576602286271946e-5
   byffi, xcwy! => 1.5593127519793547e-5
   uryyb, qvpr! => 7.955707466401606e-6
   zwddg, vauw! => 5.4773353916380185e-6
   yvccf, uztv! => 3.965247442880524e-7
   tqxxa, puoq! => 9.340624632491404e-8
   vszzc, rwqs! => 7.729225526639492e-9
==#
