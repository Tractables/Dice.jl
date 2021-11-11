using MacroTools: postwalk, @capture

export @dice_bdd, @dice_ir, @dice_run

"""
process dice code before running it
currently it makes if-then-else, &&, and || polymorphic
"""
function interpret_dice(code, mgr_choice)

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
        
        $(esc(mgr)) = $mgr_choice()
        
        $(esc(flip))(prob::Number) = 
            DistBool($(esc(mgr)), prob)
        
        $(esc(ite))(args...) =
            ifthen(args...)

        
        # transformed user code
        $transformed_code
    end
end

macro dice_bdd(code)
    interpret_dice(code, CuddMgr)
end

macro dice_ir_inter(code)
    interpret_dice(code, IrMgr)
end

macro dice_ir(code)
    quote
        to_dice_ir(@dice_ir_inter $(code))
    end
end

macro dice_run(code)
    quote
        println(run_dice(@dice_ir $(code)))
    end
end