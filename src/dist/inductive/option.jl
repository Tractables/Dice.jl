
export Opt

module Opt
    using Dice
    @type T{A} = None() | Some(A)

    Some(x) = Some(typeof(x), x)

    function bind(f, T, x::Opt.T)
        @match x [
            None() -> None(T),
            Some(x) -> f(x)
        ]
    end

    function map(f, T, x::Opt.T)
        @match x [
            None() -> None(T),
            Some(x) -> Some(T, f(x))
        ]
    end
end
