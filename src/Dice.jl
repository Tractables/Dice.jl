module Dice

include("core.jl")

include("backend/cudd.jl")
include("backend/ir.jl")

include("dsl.jl")
include("ocaml.jl")

include("lib/infer.jl")
include("lib/dwe.jl")
include("lib/int.jl")
include("lib/cond.jl")
include("lib/char.jl")
include("lib/string.jl")
include("lib/enum.jl")
include("lib/vector.jl")
include("lib/tree.jl")
# include("lib/tuple.jl")

end # module
