using Dice

f = flip(0.1)
dist_jl = infer((f, (!f, (DistInt(3), (flip(0.3))))))

# The OCaml Dice program that generated ocaml_res_ex.txt is:
# let f = flip 0.1 in (f, (!f, (int(2, 3), (flip 0.3))))
dist_ocaml = ocaml_dice_output_to_inference_result("examples/ocaml_res_ex.txt")

@assert dist_jl ≈ dist_ocaml
