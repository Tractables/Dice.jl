using Dice
using Dice: ifelse

Pollution = discrete_int([0.500000,0.400000,0.100000])
Smoker = discrete_int([0.300000,0.700000])
Cancer = ifelse(prob_equals(Pollution, DistInt(0)), ifelse(prob_equals(Smoker, DistInt(0)), discrete_int([0.030000,0.970000]), discrete_int([0.001000,0.999000])), ifelse(prob_equals(Pollution, DistInt(1)), ifelse(prob_equals(Smoker, DistInt(0)), discrete_int([0.030000,0.970000]), discrete_int([0.001000,0.999000])), ifelse(prob_equals(Smoker, DistInt(0)), discrete_int([0.050000,0.950000]), discrete_int([0.020000,0.980000]))))
Dyspnoea = ifelse(prob_equals(Cancer, DistInt(0)), discrete_int([0.650000,0.350000]), discrete_int([0.300000,0.700000]))
Xray = ifelse(prob_equals(Cancer, DistInt(0)), discrete_int([0.900000,0.100000]), discrete_int([0.200000,0.800000]))

res = infer((Xray,(Dyspnoea,(Cancer,(Smoker,Pollution)))))

# Test correctness
ocaml_res = ocaml_dice_output_to_inference_result("examples/bayesian_networks/ocaml_cancer_res.txt")
@assert res ≈ ocaml_res