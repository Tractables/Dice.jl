using DelimitedFiles

file = open("support2.txt", "w")

a = Dict{Vector{Float64}, Vector{Int64}}()
for r = 0:255
    for g = 0:255
        for b = 0:255
            y = r/4 + g/2 + b/4
            co = r/2 - b/2
            cg = -r/4 + g/2 -b/4
            if haskey(a, [y, co, cg])
                @show a[[y, co, cg]]
                @show r, g, b
            else
                a[[y, co, cg]] = [r, g, b]
            end
        end
    end
end

close(file)
