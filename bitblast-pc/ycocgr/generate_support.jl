using DelimitedFiles

file = open("bitblast-pc/ycocgr/support.txt", "w")

a = Dict{Vector{Float64}, Vector{Int64}}()
for r = 0:255
    for g = 0:255
        for b = 0:255
            y = floor(r/4 + g/2 + b/4)
            co = r - b
            cg = floor(- r/2 + g - b/2)
            if !haskey(a, [y, co, cg])
                a[[y, co, cg]] = [r, g, b]
            else 
                @show r, g, b, y, co, cg
                @show a[[y, co, cg]]
            end
        end
    end
end

@show length(a)
@assert length(a) == 2^24

for i in keys(a)
    writedlm(file, [i[1] i[2] i[3]])
end

close(file)