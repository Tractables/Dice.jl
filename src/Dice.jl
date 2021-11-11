module Dice

include("core.jl")

include("backend/cudd.jl")
include("backend/ir.jl")

include("dsl.jl")
include("ocaml.jl")

# include("lib/int.jl")
# include("lib/tuple.jl")

end # module
