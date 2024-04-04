
export Opt

module Opt
    using Dice
    import Dice: param_lists
    @inductive T{A} None() Some(A)
end