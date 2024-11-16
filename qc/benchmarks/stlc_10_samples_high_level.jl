using Revise
using Infiltrator
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
rs = RunState(Valuation(), Dict{String,ADNode}(), open(log_path, "w"), out_dir, MersenneTwister(SEED), nothing,generation_params, ADComputer(Valuation()))

prog = derive_lang_sibling_generator(generation_params)

sampler, _prim_map, _function_resutls = sample_from_lang(rs, prog)

function wellTyped(e)
    @assert isdeterministic(e)
    @match typecheck(e) [
        Some(_) -> true,
        None() -> false,
    ]
end

retries = Ref(0)
NUM_SAMPLES = 2


ProfileView.@profview sampler()


ProfileView.@profview sampler()
length(Dice.sm_cache)

empty!(Dice.sm_cache)
@elapsed sampler()

NUM_SAMPLES = 10
# begin
#== @benchmark ==# @elapsed begin
    samples = []
    while length(samples) < NUM_SAMPLES
        retries[] += 1
        s = sampler()
        if retries[] > NUM_SAMPLES * 5
            println("too many retries")
            break
        end
        if wellTyped(s)
            push!(samples, s)
        end
    end
end
retries[] 
