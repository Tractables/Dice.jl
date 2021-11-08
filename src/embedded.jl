using MacroTools: postwalk, @capture

export @dice

# extentions to Dice.jl to support embedding dice-like code in Julia

ite(cond::ProbBool, x, y) = 
    ite(cond, convert(ProbData,x), convert(ProbData,y))

Base.:&(x::ProbBool, y::Bool) = 
    x & convert(ProbBool,y)

Base.:&(x::Bool, y::ProbBool) = 
    y & x

Base.:|(x::ProbBool, y::Bool) = 
    x | convert(ProbBool,y)

Base.:|(x::Bool, y::ProbBool) = 
    y | x

Base.convert(::Type{ProbData}, b::Bool) = 
    Base.convert(ProbBool, b)

"""
macro to process dice code before running it
currently it makes if-then-else, &&, and || polymorphic
"""
macro dice(code)

    # TODO figure out how to use `esc` to correctly bind methods defined outside of the macro

    transformed_code = postwalk(code) do x
        # TODO: replace by custom desugaring that is still lazy for boolean guards
        # this will not work in general
        # for example when control flow has `return`` inside
        if x isa Expr && (x.head == :if || x.head == :elseif)
            @assert length(x.args) == 3 "@dice macro only supports purely functional if-then-else"
            return Expr(:call, :ifelse, x.args...)
        end
        @capture(x, A_ || B_) && return :($A | $B) 
        @capture(x, A_ && B_) && return :($A & $B) 
        return x
    end

    return quote
        
        # prelims tied to one manage
        mgr = Dice.default_manager()
        
        Dice.flip(prob::Number) = 
            Dice.flip(mgr) #ignore prob for now
        
        Base.convert(::Type{ProbBool}, b::Bool) = 
            Dice.ProbBool(mgr, b)
            
        # transformed user code
        $transformed_code
    end
end