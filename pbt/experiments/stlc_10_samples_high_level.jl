using Revise
using Dice
using BenchmarkTools
using ProfileView
using Profile
using PProf

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
rs = RunState(Valuation(), Dict{String,ADNode}(), open(log_path, "w"), out_dir, MersenneTwister(SEED), nothing,generation_params, ADComputer(Valuation()))

prog = derive_lang_sibling_generator(generation_params);

sampler = sample_from_lang(rs, prog)

function wellTyped(e)
    # @assert isdeterministic(e)
    @match typecheck(e) [
        Some(_) -> true,
        None() -> false,
    ]
end


function to_dist(v)
    if v isa Bool
        v
    elseif v isa Integer
        DistUInt32(v)
    elseif v isa Tuple
        ctor, args = v
        ctor([to_dist(arg) for arg in args]...)
    else
        error()
    end
end


retries = Ref(0)
NUM_SAMPLES = 200

@time begin
    retries[] = 0
    samples = []
    while length(samples) < NUM_SAMPLES
        retries[] += 1
        if retries[] > NUM_SAMPLES * 10
            println("too many retries")
            break
        end
        s = to_dist(sampler())
        if wellTyped(s)
        # s = sampler()
        # if !(typecheck(s) isa String)
            push!(samples, s)
        end
    end
end
# 1.5-5 sec


@time res, prim_map, function_results = interp(rs, prog);
# 36 sec, one-time
# g = Generation(OptExpr.Some(res))
g = res

l = Dice.LogPrExpander(WMC(BDDCompiler([
    prob_equals(g, sample)
    for sample in samples
]))) # ~156ms
a = ADComputer(rs.var_vals)

# ProfileView.profile() begin
ProfileView.@profview begin
    loss, actual_loss = sum(
        begin
            lpr_eq = Dice.expand_logprs(l, LogPr(prob_equals(g, sample)))
            [lpr_eq * compute(a, lpr_eq), lpr_eq]
        end
        for sample in samples
    )
end
# 630ms
