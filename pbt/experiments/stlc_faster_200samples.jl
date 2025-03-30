# We found sampling from the BDD, like sampling from the computation graph, also took ~160s for 200 well-typed samples.
# OTHER TIMINGS IN THIS FILE ARE WRONG
# mainly we care about `sample_one_as_dist_compile` in this file

using Revise
using Dice
using BenchmarkTools
using ProfileView

function comp_graph_size(roots)
    cmp_graph_ct = Ref(0)
    Dice.foreach_down(roots) do _
        cmp_graph_ct[] += 1
    end
    cmp_graph_ct[] # 2040
end


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

function sample_one_as_dist_compile(c::BDDCompiler, a::ADComputer, d::Dist, roots)
    # State for one sampling
    bdd_node_to_tf = Dict{CuddNode,Bool}()
    level_to_tf = Dict{Integer, Bool}()
    bdd_node_to_tf[Dice.constant(c.mgr, true)] = true
    bdd_node_to_tf[Dice.constant(c.mgr, false)] = false

    function sample_level(c, level::Integer)
        get!(level_to_tf, level) do
            prob = compute(a, c.level_to_flip[level].prob)
            rand() < prob
        end
    end

    function sample_one(c, bdd_node_to_tf, x::AnyBool)
        sample_one(c, bdd_node_to_tf, compile(c, x))
    end

    function sample_one(c, bdd_node_to_tf, x::CuddNode)
        get!(bdd_node_to_tf, x) do
            if sample_level(c, Dice.level(x))
                sample_one(c, bdd_node_to_tf, Dice.high(x))
            else
                sample_one(c, bdd_node_to_tf, Dice.low(x))
            end
        end
    end

    bits = Dict()
    for root in roots
        bits[root] = sample_one(c, bdd_node_to_tf, root)
    end
    Dice.frombits_as_dist(d, bits)
end


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
    d = g
    roots = Dice.tobits(d)
    c = BDDCompiler(roots)
    a = Dice.ADComputer(rs.var_vals)
    while length(samples) < NUM_SAMPLES
        retries[] += 1
        s = sample_one_as_dist_compile(c, a, d, roots)
        if wellTyped(s)
            push!(samples, s)
        end
    end
end
# 174s, 155s, 281
retries[] # 607, 556

@time eqs = [
    prob_equals(g, sample)
    for sample in samples
]
# 27 sec

comp_graph_size(eqs) # 2040
comp_graph_size(Dice.tobits(g)) # 16825

# @benchmark prob_equals(g, samples[1])
# BenchmarkTools.Trial: 24 samples with 1 evaluation.
#  Range (min … max):  104.068 ms … 592.294 ms  ┊ GC (min … max): 0.00% … 0.00%
#  Time  (median):     168.251 ms               ┊ GC (median):    0.00%
#  Time  (mean ± σ):   186.669 ms ±  97.022 ms  ┊ GC (mean ± σ):  0.00% ± 0.00%
#    ▃▃█  ▃▃▃ ▃▃                                                   
#   ▇███▁▁███▇██▁▇▇▁▁▇▁▁▁▁▁▇▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▇ ▁
#   104 ms           Histogram: frequency by time          592 ms <
#  Memory estimate: 6.51 MiB, allocs estimate: 235681.

@time c = BDDCompiler(eqs)
# 0.28553 s, 0.23, 0.1

@time w = WMC(c)
# instant

@time l = Dice.LogPrExpander(w)
# instant

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

