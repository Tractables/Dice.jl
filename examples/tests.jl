include("tests_h.jl")

############################ CONFIG ###########################

RESULTS_DIR = "results"
NOTES = ""

tests = Vector([
    "network" => TestInput(network(), nothing)
    "caesar" => TestInput(caesar()...)
    "grammar" => TestInput(grammar(), nothing)
    "tree" => TestInput(tree()...)
])

flip_orders = [
    FlipOrder(flips_by_instantiation_order, "inst", "inst (D)"), 
    FlipOrder(flips_left_to_right, "LTR", "RTL"),
    FlipOrder(flips_by_deepest_depth, "dd", "dd (D)"),
    FlipOrder(flips_by_shallowest_depth, "sd", "sd (D)"), 
    FlipOrder(flips_by_freq, "freq", "freq (D)")
]

###############################################################


if !isdir(RESULTS_DIR)
    mkdir(RESULTS_DIR)
end
dir = RESULTS_DIR * "/" * Dates.format(now(), "yyyy-mm-dd_HH-MM-SS")
mkdir(dir)

if length(NOTES) > 0
    touch(RESULTS_DIR * "/" * NOTES)
end
log_file = open(dir * "/" * "log.txt", "w")

header = vcat(["name"], Iterators.flatten((fo.name, fo.name_reversed) for fo in flip_orders)...)
results_num_nodes = Vector{Any}([header])
results_num_inferences = Vector{Any}([header])
results_nodes_per = Vector{Any}([header])
results_inf = Vector{Any}([header])

for (test_name, test) in tests
    println("Starting test $(test_name)")
    result_num_nodes = Vector{Any}([test_name])
    result_num_inferences = Vector{Any}([test_name])
    result_nodes_per = Vector{Any}([test_name])
    result_inf = Vector{Any}([test_name])

    write(log_file, "Starting test $(test_name)\n")
    for flip_order in flip_orders
        println(flip_order.order_func)
        write(log_file, "FO: $(flip_order.order_func)\n")
        for rev in (false, true)
            write(log_file, "Rev: $(rev)\n")
            # println(rev)
            boolsable = if test.observe === nothing
                test.computation_graph
            else
                test.computation_graph, test.observe
            end
            mgr, to_bdd = dist_to_mgr_and_compiler(boolsable; flip_order=flip_order.order_func, flip_order_reverse=rev)
            nn = []
            function inferer(d)
                push!(
                    nn,
                    num_nodes(mgr, map(to_bdd, bools(d)))
                )
                infer_bool(mgr, to_bdd(d))
            end
            inf_res = if test.observe === nothing
                infer(inferer, test.computation_graph)
            else
                infer_with_observation(inferer, test.computation_graph, test.observe)
            end
            write_inf_res(log_file, inf_res)
            write(log_file, "\n")

            push!(result_num_nodes, num_nodes(mgr, map(to_bdd, bools(boolsable))))
            push!(result_num_inferences, length(nn))
            push!(result_nodes_per, sum(nn))
            push!(result_inf, hash_inf_res(inf_res))
            println(sum(nn))
        end
    end
    push!(results_num_nodes, result_num_nodes)
    push!(results_num_inferences, result_num_inferences)
    push!(results_nodes_per, result_nodes_per)
    push!(results_inf, result_inf)
    flush(log_file)
end

results_to_csv("$(dir)/num_nodes.csv", results_num_nodes)
results_to_csv("$(dir)/num_inferences.csv", results_num_inferences)
results_to_csv("$(dir)/num_nodes_total.csv", results_nodes_per)
results_to_csv("$(dir)/inf_hashes.csv", results_inf)

results_to_latex("$(dir)/num_nodes_total.txt", results_nodes_per)

close(log_file)