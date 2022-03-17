module Dice

include("core.jl")

include("backend/cudd.jl")
include("backend/ir.jl")

include("dsl.jl")
include("ocaml.jl")

include("lib/int.jl")
include("lib/cond.jl")
include("lib/fixedpoint.jl")
include("lib/signedint.jl")
include("lib/fixedpointparam.jl")
include("lib/basic.jl")
# include("lib/tuple.jl")

end # module
