using MacroTools: postwalk, @capture

export @dice

# extentions to Dice.jl to support embedding dice-like code in Julia

ite(cond::ProbBool, x, y) = 
    ite(cond, val2dist(x, cond.mgr), 
              val2dist(y, cond.mgr))

Base.:&(x::ProbBool, y::Bool) = 
    x & val2dist(y, x.mgr)

Base.:&(x::Bool, y::ProbBool) = 
    y & x

Base.:|(x::ProbBool, y::Bool) = 
    x | val2dist(y, x.mgr)

Base.:|(x::Bool, y::ProbBool) = 
    y | x

val2dist(x::Bool, mgr) = 
    ProbBool(mgr, x)

"""
macro to process dice code before running it
currently it makes if-then-else, &&, and || polymorphic
"""
macro dice(code)

    # manual hygiene
    mgr = gensym(:mgr)
    flip = gensym(:flip)

    transformed_code = postwalk(esc(code)) do x
        # TODO: replace by custom desugaring that is still lazy for boolean guards
        # this will not work in general
        # for example when control flow has `return`` inside
        if x isa Expr && (x.head == :if || x.head == :elseif)
            @assert length(x.args) == 3 "@dice macro only supports purely functional if-then-else"
            return Expr(:call, :ifelse, x.args...)
        end
        @capture(x, flip(P_)) && return :($flip($P)) 
        @capture(x, A_ || B_) && return :($A | $B) 
        @capture(x, A_ && B_) && return :($A & $B) 
        return x
    end

    return quote
        
        $(esc(mgr)) = default_manager()
        
        function $(esc(flip))(prob::Number) 
            Dice.flip($(esc(mgr))) #ignore prob for now
        end

        # transformed user code
        $transformed_code
    end
end