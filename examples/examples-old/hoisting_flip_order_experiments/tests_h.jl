using Alea
using Dates

struct TestInput
    name::String
    computation_graph::Union{Dist, DWE}
    observe::Union{DistBool, Nothing}
end

struct FlipOrder
    order_func::Function
    name::String
    name_reversed::String
end

struct TestParams
    order::FlipOrder
    reverse::Bool
    hoist::Bool
end

include("network_verification.jl")
include("grammar_recursive.jl")
include("parser_tree.jl")
include("caesar_ex_str.jl")
include("bwh_unif.jl")


function results_to_csv(name, results)
    open(name, "w") do file
        write(file, join([join(row, ',') for row in results], '\n'))
    end
end

function results_to_latex(name, results)
    open(name, "w") do file
        # write(file, "| c !{\\vrule width 3\\arrayrulewidth}")
        # for i in 2:length(results[1])
        #     write(file, " c |")
        # end
        write(file, "\\hline\n")
        write(file, join(results[1], " & "))
        write(file, "\\\\\n\\Xhline{3\\arrayrulewidth}\n")
        for row in results[2:end]
            write(file, join(row, " & "))
            write(file, "\\\\\n\\hline\n")
        end
    end
end

function hash_inf_res(inf_res, digits=5)
    if inf_res isa Tuple
        hash([hash_dist(inf_res[1], digits), round(inf_res[2], digits=digits)])
    else
        hash_dist(inf_res, digits)
    end
end

function hash_dist(d, digits)
    d = sort(collect(d), by= xv -> -xv[2])  # by decreasing probability
    hash([(k, round(v, digits=digits)) for (k, v) in d])
end 

function write_inf_res(file, inf_res, digits=5)
    dist, err = if inf_res isa Tuple
        inf_res
    else
        inf_res, 0
    end
    write(file, "Error: $(round(err, digits=digits))\n")
    write_dist(file, dist, digits)
end

function write_dist(file, d, digits)
    d = sort(collect(d), by= xv -> -xv[2])  # by decreasing probability
    write(file, "$(typeof(d)) with $(length(d)) entries\n")
    widest = if length(d) > 0 maximum(length(string(k)) for (k, _) in d) else 0 end
    for (k, v) in d
        write(file, "   $(rpad(k, widest, ' ')) => $(round(v, digits=digits))\n")
    end
end 
