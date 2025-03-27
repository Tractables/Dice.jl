using Alea

for discrete_impl in [discrete, discrete_sbk]
    local dist, err = infer(discrete_impl([
        (DistString("abc"), 0.3),
        (DistString(""), 0.1),
        (DistString("dice"), 0.2),
        (DistString("no"), 0.),
        (DistString("fifth"), 0.4),
    ]))
    @assert err == 0
    @assert length(dist) == 4
    @assert dist["abc"] ≈ 0.3
    @assert dist[""] ≈ 0.1
    @assert dist["dice"] ≈ 0.2
    @assert dist["fifth"] ≈ 0.4
end
@assert infer_int(uniform_int(1:5)) ≈ [0., .2, .2, .2, .2, .2, 0., 0.]

for discrete_int_impl in [discrete_int, discrete_int_sbk]
    @assert infer_int(discrete_int_impl([.1, .2, .3, .4])) ≈ [.1, .2, .3, .4]
end
