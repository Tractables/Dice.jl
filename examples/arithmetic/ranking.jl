using Dice

uniq_count = 4
half = Int(ceil(uniq_count/2))
bits = Int(floor(log2(uniq_count)) + 4)
data_count = 1

# input_file = open("scratch/sushi/aa")
# skip = readline(input_file) 
# rankings = Vector(undef, data_count)
# for i = 1:data_count
#     line = readline(input_file)
#     etc = split(line, " ")
#     data = map(x -> parse(Int64, x), convert(Vector{String}, etc[3:end]))
#     rankings[i] = dataz``
rankings = [[3, 2, 1, 0], 
            [1, 3, 2, 0],
            [1, 2, 3, 0]]

c = @dice begin 
    ranks = [uniform(DistInt{bits}, 0, uniq_count) for i in 1:uniq_count]
    for i in 1:uniq_count
        for j in i+1:uniq_count
            observe(!prob_equals(ranks[i], ranks[j]))
        end
    end
    

    for data in rankings 
        obs_rank = [x + uniform(DistInt{bits}, -uniq_count, uniq_count+1) for x in ranks]
        for i in 1:uniq_count-1
            a, b = data[i]+1, data[i+1] + 1
            observe(obs_rank[a] < obs_rank[b])
        end 
    end 

    (ranks[1], ranks[2], ranks[3], ranks[4])
end


@show sort(collect(pr(c)), by=x->x[2])