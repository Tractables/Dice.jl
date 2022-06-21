include("tests_h.jl")

############################ CONFIG ###########################

RESULTS_DIR = "results"
NOTES = "deleteme"

tests_inputs = [
    TestInput("network", network(), nothing)
    # TestInput("bwh_unif", bwh_discrete32, nothing)
    # # TestInput("caesar", caesar()...)
    # TestInput("grammar", grammar(), nothing)
    # TestInput("tree", tree()...)
]

tests = [
    TestParams(fo, false, hoist)
    for rev in (false,)#true)
    for fo in [
        FlipOrder(flips_by_instantiation_order, "inst", "inst (D)"), 
        FlipOrder(flips_left_to_right, "LTR", "RTL"),
        FlipOrder(flips_by_deepest_depth, "dd", "dd (D)"),
        FlipOrder(flips_by_shallowest_depth, "sd", "sd (D)"), 
        FlipOrder(flips_by_freq, "freq", "freq (D)")
    ]
    for hoist in (false, true)
]

###############################################################


if !isdir(RESULTS_DIR)
    mkdir(RESULTS_DIR)
end
dir = RESULTS_DIR * "/" * Dates.format(now(), "yyyy-mm-dd_HH-MM-SS") * " " * NOTES
mkdir(dir)

open(dir * "/" * "hyperparams.txt", "w") do file
    write(file, "Tests:\n")
    write(file, string(tests))
    write(file, "\n\nTest inputs:\n")
    write(file, string(tests_inputs))
end

log_file = open(dir * "/" * "log.txt", "w")

header = vcat(["name"], [
    ((if test.reverse test.order.name_reversed else test.order.name end)
    * (if test.hoist " + h" else "" end))
    for test in tests
])
results_num_nodes = Vector{Any}([header])
results_num_flips = Vector{Any}([header])
results_num_inferences = Vector{Any}([header])
results_nodes_per = Vector{Any}([header])
results_inf = Vector{Any}([header])

for ti in tests_inputs
    println("Starting test $(ti.name)")
    result_num_nodes = Vector{Any}([ti.name])
    result_num_flips = Vector{Any}([ti.name])
    result_num_inferences = Vector{Any}([ti.name])
    result_nodes_per = Vector{Any}([ti.name])
    result_inf = Vector{Any}([ti.name])
    write(log_file, "Starting test $(ti.name)\n")
    for test in tests
        flip_order = test.order
        println("FO: $(flip_order.order_func)")
        println("Rev: $(test.reverse)")
        println("Hoist: $(test.hoist)")
        write(log_file, "FO: $(flip_order.order_func)\n")
        write(log_file, "Rev: $(test.reverse)\n")
        write(log_file, "Hoist: $(test.hoist)\n")
        # println(rev)
        boolsable = if ti.observe === nothing
            ti.computation_graph
        else
            ti.computation_graph, ti.observe
        end
        if test.hoist
            hoist!(boolsable)
        end
        push!(result_num_flips, num_flips(boolsable))
        mgr, to_bdd = dist_to_mgr_and_compiler(boolsable;
                                               flip_order=flip_order.order_func,
                                               flip_order_reverse=test.reverse)
        nn = []
        function inferer(d)
            push!(
                nn,
                num_nodes(mgr, map(to_bdd, bools(d)))
            )
            infer_bool(mgr, to_bdd(d))
        end
        inf_res = if ti.observe === nothing
            infer(inferer, ti.computation_graph)
        else
            infer_with_observation(inferer, ti.computation_graph, ti.observe)
        end
        write_inf_res(log_file, inf_res)
        write(log_file, "\n")

        push!(result_num_nodes, num_nodes(mgr, map(to_bdd, bools(boolsable))))
        push!(result_num_inferences, length(nn))
        push!(result_nodes_per, sum(nn))
        push!(result_inf, hash_inf_res(inf_res))
        
        println(sum(nn))
    end
    push!(results_num_nodes, result_num_nodes)
    push!(results_num_flips, result_num_flips)
    push!(results_num_inferences, result_num_inferences)
    push!(results_nodes_per, result_nodes_per)
    push!(results_inf, result_inf)
    flush(log_file)
end

results_to_csv("$(dir)/num_nodes.csv", results_num_nodes)
results_to_csv("$(dir)/num_inferences.csv", results_num_inferences)
results_to_csv("$(dir)/num_nodes_total.csv", results_nodes_per)
results_to_csv("$(dir)/num_flips.csv", results_num_flips)
results_to_csv("$(dir)/inf_hashes.csv", results_inf)

results_to_latex("$(dir)/num_nodes_total.txt", results_nodes_per)

close(log_file)