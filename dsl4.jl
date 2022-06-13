using Dice
using IfElse: ifelse

# TODO turn into a unit test later

foo(x) = ifelse(flip(x), flip(x/2), flip(x/4))
foo(0.9)

foo(x) = flip(x) ? flip(x/2) : flip(x/4)
foo(0.9) # error

using IRTools
using IRTools: @dynamo, IR, recurse!

# pirate `IRTools.cond`` but keep default behavior on Bool guards
IRTools.cond(guard::Bool, then, elze) = guard ? then() : elze()
IRTools.cond(guard, then, elze) = ifelse(guard, then(), elze())

@dynamo function dice(a...)
    ir = IR(a...)
    (ir == nothing) && return
    recurse!(ir, dice)
    return IRTools.functional(ir)
end

# avoid transformation when it is known to trigger a bug

dice(::typeof(unsafe_copyto!), args...) = unsafe_copyto!(args...)

dice() do 
    foo(0.9)
end