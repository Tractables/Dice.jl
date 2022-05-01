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
    ite = gensym(:ite)
    ite_guard = gensym(:ite)

    transformed_code = postwalk(esc(code)) do x
        # TODO: replace by custom desugaring that is still lazy for boolean guards
        # this will not work in general
        # for example when control flow has `return`` inside
        if x isa Expr && (x.head == :if || x.head == :elseif)
            @assert length(x.args) == 3 "@dice macro only supports purely functional if-then-else"
            # return :($ite($(x.args...)))
            return :(begin $ite_guard = $(x.args[1])
                    if ($(ite_guard) isa DistBool)
                        Dice.ifelse($(ite_guard), $(x.args[2:3]...))
                    else
                        (if $(ite_guard)
                            $(x.args[2])
                        else
                            $(x.args[3])
                        end)
                    end
                end)
        end
        @capture(x, flip(P_)) && return :(DistBool($mgr, $P)) 
        @capture(x, DistInt(I_)) && return :(DistInt($mgr, $I)) 
        @capture(x, DistChar(C_)) && return :(DistChar($mgr, $C))
        @capture(x, DistString(C_)) && return :(DistString($mgr, $C))
        @capture(x, DistEnum(C_)) && return :(DistEnum($mgr, $C))
        @capture(x, DistVector(V_)) && return :(DistVector($mgr, $V))
        @capture(x, dicecontext()) && return :($mgr) 
        @capture(x, A_ || B_) && return :($A | $B) 
        @capture(x, A_ && B_) && return :($A & $B) 
        return x
    end

    return quote
        
        DiceCode( $(esc(mgr)) -> begin
        
            # $(esc(ite))(args...) = 
            #     if typeof(args[1]) == DistBool
            #         ifelse(args...)
            #     else
            #         if args[1]
            #             args[2]
            #         else
            #             args[3]
            #         end
            #     end

            
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
