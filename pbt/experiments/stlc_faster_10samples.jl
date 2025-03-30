using Revise
using Dice
using BenchmarkTools
using ProfileView

include("benchmarks.jl")

generation_params = LangSiblingDerivedGenerator{STLC}(
    root_ty=Expr.t,
    ty_sizes=[Expr.t=>5, Typ.t=>2],
    stack_size=2,
    intwidth=3,
)

SEED = 0
out_dir="/tmp"
log_path="/dev/null"
rs = RunState(Valuation(), Dict{String,ADNode}(), open(log_path, "w"), out_dir, MersenneTwister(SEED), nothing,generation_params)

prog = derive_lang_sibling_generator(generation_params)

sample_from_lang(rs, prog)

generation::Generation = generate(rs, generation_params)

g::Dist = generation.value

rs.var_vals


# Sample some tree until it's valid (TODO: make this faster)
a = ADComputer(rs.var_vals)

sample_cache = Dict{Dist{Bool}, Bool}()





s = better_sample(rs.rng, a, g, sample_cache)


@dice_ite if f
    DistUInt{3}([a, b, c])
else
    DistUInt{3}([d, e, f])
end

# evaluates to...

DistIte(
    f,
    DistUInt{3}([a, b, c]),
    DistUInt{3}([d, e, f])
)

# during compilation, we lower it to...


# for Coq-like sampling
# 1. dist-aware sample - each dist type defines its own short-circuiting sample method
# 2. we save ifs as a special dist type

DistUInt{3}([ite(f,a,d),ite(f,b,e),ite(f,c,f)])


DistTaggedUnion(
    which=DistUInt{1}(flip(0.5)),
    dists=[ugly1(), ugly2()],
)


DistIte{}

# REMEMBER TO DISABLE ASSERTS
NUM_SAMPLES = 10

function wellTyped(e)
    @assert isdeterministic(e)
    @match typecheck(e) [
        Some(_) -> true,
        None() -> false,
    ]
end

retries = Ref(0)
#== @benchmark ==# @elapsed begin
    samples = []
    while length(samples) < NUM_SAMPLES
        retries[] += 1
        s = sample_as_dist(rs.rng, a, g)
        if wellTyped(s)
            push!(samples, s)
        end
    end
end
#  Single result which took 26.426 s (3.00% GC) to evaluate, (7s, 26s, 30s, 40s)
#  with a memory estimate of 388.02 MiB, over 8512429 allocations.
retries[] # 30 

l = Dice.LogPrExpander(WMC(BDDCompiler([
    prob_equals(g, sample)
    for sample in samples
])))
@time begin
    loss, actual_loss = sum(
        begin
            lpr_eq = Dice.expand_logprs(l, LogPr(prob_equals(g, sample)))
            [lpr_eq * compute(a, lpr_eq), lpr_eq]
        end
        for sample in samples
    )
end
# 5.3s first run, 1.4s rest

length(l.cache) # 331

@benchmark vals, derivs = differentiate(
    rs.var_vals,
    Derivs([loss => 1.])
)
# BenchmarkTools.Trial: 1060 samples with 1 evaluation.
#  Range (min … max):  2.029 ms … 137.030 ms  ┊ GC (min … max): 0.00% … 98.14%
#  Time  (median):     2.879 ms               ┊ GC (median):    0.00%
#  Time  (mean ± σ):   4.377 ms ±   6.119 ms  ┊ GC (mean ± σ):  4.36% ±  4.07%

#   ██▇▆▅▃▃▂▃▁▁▂▂  ▁                                             
#   ██████████████████▅▇▆▄▆▄▆▇▄▆▄▅▁▆▁▅▇▁▄▄▁▁▁▄▁▁▅▄▆▁▄▄▁▁▁▄▁▁▁▅▅ █
#   2.03 ms      Histogram: log(frequency) by time      22.6 ms <

#  Memory estimate: 292.17 KiB, allocs estimate: 8034.

ct = Ref(0)
Dice.foreach_down(loss) do _ ct[] += 1 end
ct[] # 350

