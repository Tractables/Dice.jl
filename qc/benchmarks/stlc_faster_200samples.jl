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

generation::Generation = generate(rs, generation_params)

g::Dist = generation.value

# Sample some tree until it's valid (TODO: make this faster)
a = ADComputer(rs.var_vals)

NUM_SAMPLES = 200

function wellTyped(e)
    @assert isdeterministic(e)
    @match typecheck(e) [
        Some(_) -> true,
        None() -> false,
    ]
end

retries = Ref(0)
#== @benchmark ==# @time begin
    samples = []
    while length(samples) < NUM_SAMPLES
        retries[] += 1
        s = sample_as_dist(rs.rng, a, g)
        if wellTyped(s)
            push!(samples, s)
        end
    end
end
# 174s, 155s
retries[] # 607, 556

@time l = Dice.LogPrExpander(WMC(BDDCompiler([
    prob_equals(g, sample)
    for sample in samples
])))
# 32s, 36s

@time loss, actual_loss = sum(
    begin
        lpr_eq = Dice.expand_logprs(l, LogPr(prob_equals(g, sample)))
        [lpr_eq * compute(a, lpr_eq), lpr_eq]
    end
    for sample in samples
)
# 6s, 31s, 9s

length(l.cache) # 3473

@benchmark vals, derivs = differentiate(
    rs.var_vals,
    Derivs([loss => 1.])
)
# BenchmarkTools.Trial: 113 samples with 1 evaluation.
#  Range (min … max):  21.161 ms … 130.908 ms  ┊ GC (min … max): 0.00% … 30.08%
#  Time  (median):     39.090 ms               ┊ GC (median):    0.00%
#  Time  (mean ± σ):   44.209 ms ±  18.477 ms  ┊ GC (mean ± σ):  0.79% ±  2.83%
#      ▁▄ ▂▅█▁▅▇     ▂  ▁                                         
#   ▃▅▁██▆███████▆▅█▃█▆▅█▆▃▃▅▅▃▅▁▁▁▃▁▁▁▃▃▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▃▁▁▁▃▃ ▃
#   21.2 ms         Histogram: frequency by time          117 ms <
#  Memory estimate: 2.11 MiB, allocs estimate: 62283.

ct = Ref(0)
Dice.foreach_down(loss) do _ ct[] += 1 end
ct[] # 3872

