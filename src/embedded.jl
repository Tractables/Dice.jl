using MacroTools: postwalk, @capture

export @dice

# extentions to Dice.jl to support embedding dice-like code in Julia

ite(cond::ProbBool, x, y) = 
    ite(cond, val2dist(x, cond.mgr), 
              val2dist(y, cond.mgr))

ite(cond::ProbBool, x::ProbBool, y) = 
    ite(cond, x, val2dist(y, cond.mgr))

ite(cond::ProbBool, x, y::ProbBool) = 
    ite(cond, val2dist(x, cond.mgr), y)
                                
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
macro dice(analysis, code)

    # manual hygiene
    mgr = gensym(:mgr)
    flip = gensym(:flip)
    ite = gensym(:ite)

    transformed_code = postwalk(esc(code)) do x
        # TODO: replace by custom desugaring that is still lazy for boolean guards
        # this will not work in general
        # for example when control flow has `return`` inside
        if x isa Expr && (x.head == :if || x.head == :elseif)
            @assert length(x.args) == 3 "@dice macro only supports purely functional if-then-else"
            return :($ite($(x.args...)))
        end
        @capture(x, flip(P_)) && return :($flip($P)) 
        @capture(x, A_ || B_) && return :($A | $B) 
        @capture(x, A_ && B_) && return :($A & $B) 
        return x
    end

    mgr_choice = if eval(analysis) == :bdd
        :(default_manager())
    elseif eval(analysis) == :ir
        :(ir_manager())
    else
        error("Unknown dice analysis: ", analysis)
    end

    return quote
        
        $(esc(mgr)) = $mgr_choice
        
        $(esc(flip))(prob::Number) = 
            Dice.flip($(esc(mgr)), prob)
        
        $(esc(ite))(args...) =
            Dice.ite(args...)

        
        # transformed user code
        $transformed_code
    end
end

macro dice_ir(code)
    quote
        to_dice_ir(@dice :ir $(code))
    end
end