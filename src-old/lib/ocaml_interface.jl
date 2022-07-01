export ocaml_dice_output_to_inference_result

function ocaml_dice_output_to_inference_result(filename::String)
    ocaml_dice_output_to_inference_result(readlines(filename))
end

function ocaml_dice_output_to_inference_result(lines::Vector{String})
    @assert contains(lines[1], "[ Joint Distribution ]")
    @assert contains(lines[2], "Value\tProbability")
    dist = Dict()
    for line in lines[3:end]
        line == "" && continue
        val_str, p_str = split(line, '\t')
        # TODO: parse only tups/bools/ints to avoid arbitrary code execution
        val = eval(Meta.parse(val_str))
        p = parse(Float64, p_str)
        p != 0 && (dist[val] = p)
    end
    InferenceResult(dist, 0.)
end

# TODO: implement to_ocaml_dice(::DistBool) and to_ocaml_dice(::DistInt)
