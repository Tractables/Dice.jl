module Dice

include("core.jl")
include("dsl.jl")
include("ocaml.jl")

include("lib/int.jl")
include("lib/char.jl")
include("lib/string.jl")
include("lib/enum.jl")
include("lib/vector.jl")
include("lib/tree.jl")
# include("lib/tuple.jl")

include("inference/infer.jl")
include("inference/cudd.jl")
include("inference/dwe.jl")
include("inference/cond.jl")

end # module
