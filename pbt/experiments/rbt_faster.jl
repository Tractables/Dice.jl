using Revise
using Dice
include("benchmarks.jl")

generation_params = LangSiblingDerivedGenerator{RBT}(
    root_ty=ColorKVTree.t,
    ty_sizes=[ColorKVTree.t=>4, Color.t=>0],
    stack_size=2,
    intwidth=3,
)

SEED = 0
out_dir="/tmp"
log_path="/dev/null"
rs = RunState(Valuation(), Dict{String,ADNode}(), open(log_path, "w"), out_dir, MersenneTwister(SEED), nothing,generation_params)

generation::Generation = generate(rs, generation_params)

g::Dist = generation.value

# Assignments
# rs.var_vals

# Distribution of constructors of root node:
pr_mixed(rs.var_vals)(g.union.which)

# Sample some tree until it's valid (TODO: make this faster)
a = ADComputer(rs.var_vals)
isRBT(t) = satisfies_bookkeeping_invariant(t) && satisfies_balance_invariant(t) && satisfies_order_invariant(t)
using BenchmarkTools

@benchmark begin
   samples = []
    while length(samples) < 200
        some_tree = sample_as_dist(rs.rng, a, g)
        if isRBT(some_tree)
            push!(samples, some_tree)
        end
    end
end

# one sample
# BenchmarkTools.Trial: 1683 samples with 1 evaluation.
#  Range (min … max):  1.789 ms … 29.207 ms  ┊ GC (min … max): 0.00% … 77.88%
#  Time  (median):     2.012 ms              ┊ GC (median):    0.00%
#  Time  (mean ± σ):   2.895 ms ±  2.100 ms  ┊ GC (mean ± σ):  4.64% ±  7.26%

#   █▇▅▃      ▃▅▃▂▃▁     ▁▂▂▁                                   
#   █████▆▄▁▁▁██████▇▆▁▄▆████▇▇▇▅▇▄▇▇▅▆▆▅▅▇▄▄▅▅▅▆▄▆▄▁▁▄▄▅▁▄▄▁▄ █
#   1.79 ms      Histogram: log(frequency) by time     8.87 ms <

#  Memory estimate: 759.81 KiB, allocs estimate: 19182.

# 200 samples
# BenchmarkTools.Trial: 9 samples with 1 evaluation.
#  Range (min … max):  551.427 ms … 637.939 ms  ┊ GC (min … max): 3.72% … 6.07%
#  Time  (median):     571.511 ms               ┊ GC (median):    3.63%
#  Time  (mean ± σ):   577.534 ms ±  29.908 ms  ┊ GC (mean ± σ):  4.56% ± 1.59%

#   █             ▃                                                
#   █▁▁▁▁▇▁▁▁▁▁▁▁▁█▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▇▁▁▁▁▁▁▇▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▇ ▁
#   551 ms           Histogram: frequency by time          638 ms <

#  Memory estimate: 207.46 MiB, allocs estimate: 5280362.

some_tree

# .551 * 1000 / 60 ~= 9 minutes on sampling


# Every other epoch, we spend 1/2 a second taking ~300 samples in order to get
# exactly 200 samples that meet the spec.

# "smart conditional sampling" saves at most 2/9 of runtime for RBT

# time per epoch: ~.25

retries = 0
samples = []
while length(samples) < 200
    retries +=1
    some_tree = sample_as_dist(rs.rng, a, g)
    if isRBT(some_tree)
        push!(samples, some_tree)
    end
end

retries # 321 samples taken


l = Dice.LogPrExpander(WMC(BDDCompiler([
    prob_equals(g,sample)
    for sample in samples
])))

num_meeting = 0
@time begin
    loss, actual_loss = sum(
        begin
        lpr_eq = Dice.expand_logprs(l, LogPr(prob_equals(g, sample)))
        [lpr_eq * compute(a, lpr_eq), lpr_eq]
        end
        for sample in samples
    )
end
# 1.74s on first run, ~.5 seconds on later runs

length(l.cache) # 935

# 0.165 seconds first time


@benchmark vals, derivs = differentiate(
    rs.var_vals,
    Derivs([loss => 1.])
)

# BenchmarkTools.Trial: 1867 samples with 1 evaluation.
#  Range (min … max):  2.441 ms … 23.635 ms  ┊ GC (min … max): 0.00% … 88.88%
#  Time  (median):     2.544 ms              ┊ GC (median):    0.00%
#  Time  (mean ± σ):   2.634 ms ±  1.110 ms  ┊ GC (mean ± σ):  2.54% ±  5.30%

#      ▁▁▁▅▆▆▆▇█▇▅▇▂▂                                           
#   ▃▄▆████████████████▇▇▆▆▆▅▅▄▄▄▄▃▄▃▃▃▃▃▃▃▃▃▃▃▃▃▂▃▃▃▃▂▂▂▁▂▂▂▂ ▄
#   2.44 ms        Histogram: frequency by time         2.9 ms <

#  Memory estimate: 635.62 KiB, allocs estimate: 19618.

ct = [0]
Dice.foreach_down(loss) do _
    ct[1] += 1
end
ct # 1334

p_eq_g = prob_equals(some_tree, g)
to_maximize::Dice.ADNode = LogPr(p_eq_g)
using ProfileView

pr_mixed(rs.var_vals)(p_eq_g)

l = Dice.LogPrExpander(WMC(BDDCompiler(Dice.bool_roots([to_maximize]))))
to_maximize_expanded = Dice.expand_logprs(l, to_maximize)

using ProfileView

ProfileView.@profview begin
    vals, derivs = Dice.differentiate(
        rs.var_vals,
        Derivs(to_maximize_expanded => 1.)
    )
end

