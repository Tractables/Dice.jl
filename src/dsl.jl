using MacroTools: postwalk, @capture

export @dice, compile, rundice

struct DiceCode
    interpret::Function
end

"""
process dice code before running it
currently it makes if-then-else, &&, and || polymorphic
"""
function to_dice(code)

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

    return quote
        
        DiceCode( $(esc(mgr)) -> begin
        
            $(esc(flip))(prob::Number) = 
                DistBool($(esc(mgr)), prob)
            
            $(esc(ite))(args...) =
                ifelse(args...)
            
            # transformed user code
            $transformed_code
        end)
    end
end

macro dice(code)
    to_dice(code)
end

function compile(code::DiceCode)
    code.interpret(CuddMgr())
end

function to_dice_ir(code::DiceCode)
    interpretation = code.interpret(IrMgr())
    treeify(interpretation.bit)
end

function rundice(code::DiceCode)
    rundice(to_dice_ir(code)) 
end

function infer(code::DiceCode, algo)
    x = if algo == :ocaml
        to_dice_ir(code)
    elseif algo == :bdd
        compile(code)
    end
    infer(x) 
end
