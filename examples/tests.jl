using Dice
include("network_verification.jl")
include("grammar_recursive.jl")
include("parser_tree.jl")
include("caesar_ex_str.jl")

struct TestInput
    computation_graph::Union{Dist, DWE}
    observe::Union{DistBool, Nothing}
end

tests = Vector([
    "network" => TestInput(network(), nothing)
    "caesar" => TestInput(caesar()...)
    "grammar" => TestInput(grammar(), nothing)
    "tree" => TestInput(tree()...)
])

flip_orders = [flips_by_instantiation_order, flips_left_to_right,
    flips_by_deepest_depth, flips_by_shallowest_depth, flips_by_freq]

header = ["name", "age", "age (D)", "LTR", "RTL", "deepest depth", "deepest depth (desc)", "shallowest depth", "by shallowest depth (desc)", "freq", "freq (desc)"]
results_num_nodes = Vector{Any}([header])
results_num_inferences = Vector{Any}([header])
results_nodes_per = Vector{Any}([header])

for (test_name, test) in tests
    println("Starting test $(test_name)")
    result_num_nodes = Vector{Any}([test_name])
    result_num_inferences = Vector{Any}([test_name])
    result_nodes_per = Vector{Any}([test_name])
    for flip_order in flip_orders
        println(flip_order)
        for rev in (false, true)
            # println(rev)
            boolsable = if test.observe === nothing
                test.computation_graph
            else
                test.computation_graph, test.observe
            end
            mgr, to_bdd = dist_to_mgr_and_compiler(boolsable; flip_order=flip_order, flip_order_reverse=rev)
            nn = []
            dist, error = if test.observe === nothing
                infer(test.computation_graph) do d
                    push!(
                        nn,
                        num_nodes(mgr, map(to_bdd, bools(d)))
                    )
                    infer_bool(mgr, to_bdd(d))
                end
            else
                infer_with_observation(test.computation_graph, test.observe) do d
                    push!(
                        nn,
                        num_nodes(mgr, map(to_bdd, bools(d)))
                    )
                    infer_bool(mgr, to_bdd(d))
                end
            end

            push!(result_num_nodes, num_nodes(mgr, map(to_bdd, bools(boolsable))))
            push!(result_num_inferences, length(nn))
            push!(result_nodes_per, sum(nn))
            println(sum(nn))
        end
    end
    push!(results_num_nodes, result_num_nodes)
    push!(results_num_inferences, result_num_inferences)
    push!(results_nodes_per, result_nodes_per)
end

function results_to_csv(name, results)
    open(name, "w") do file
        write(file, join([join(row, ',') for row in results], '\n'))
    end
end

results_to_csv("num_nodes.csv", results_num_nodes)
results_to_csv("num_inferences.csv", results_num_inferences)
results_to_csv("num_nodes_avg.csv", results_nodes_per)



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

results_to_latex("num_nodes_avg.txt", results_nodes_per)