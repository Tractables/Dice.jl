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

ProfileView.@profview println(@elapsed sampler())

# @elapsed s = sampler()
# @elapsed d = to_dist(s)
# @elapsed wellTyped(d)

length(Dice.sm_cache)

empty!(Dice.sm_cache)
@elapsed sampler()

sampler()

NUM_SAMPLES = 200

s = sampler()
typecheck(s)
s

# begin
@benchmark begin
    retries[] = 0
    samples = []
    while length(samples) < NUM_SAMPLES
        retries[] += 1
        if retries[] > NUM_SAMPLES * 10
            println("too many retries")
            break
        end
        # s = to_dist(sampler())
        # if wellTyped(s)
        s = sampler()
        if !(typecheck(s) isa String)
            push!(samples, s)
        end
    end
end
#==
BenchmarkTools.Trial: 25 samples with 1 evaluation.
 Range (min … max):  147.637 ms … 739.791 ms  ┊ GC (min … max):  0.00% … 70.03%
 Time  (median):     167.911 ms               ┊ GC (median):     0.00%
 Time  (mean ± σ):   195.221 ms ± 115.256 ms  ┊ GC (mean ± σ):  10.61% ± 14.01%

  ██▆ ▃                                                          
  ███▄█▁▁▁▇▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▄ ▁
  148 ms           Histogram: frequency by time          740 ms <

 Memory estimate: 28.02 MiB, allocs estimate: 919029.
==#


@benchmark begin
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
#==
BenchmarkTools.Trial: 4 samples with 1 evaluation.
 Range (min … max):  1.143 s …    1.559 s  ┊ GC (min … max): 0.00% … 0.00%
 Time  (median):     1.281 s               ┊ GC (median):    0.00%
 Time  (mean ± σ):   1.316 s ± 195.134 ms  ┊ GC (mean ± σ):  0.00% ± 0.00%

  █   █                             █                      █  
  █▁▁▁█▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁█▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁█ ▁
  1.14 s         Histogram: frequency by time         1.56 s <

 Memory estimate: 37.10 MiB, allocs estimate: 1142548.

==#



@ProfileView.profview begin
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
