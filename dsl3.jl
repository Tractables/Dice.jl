using IRTools

##################

function foo(x,y)
    z = y+0.05
    if x
        0.4 + z
    else
        0.1 + z
    end
end

ifelse(g::AbstractFloat, t, e) = g*t + (1-g)*e

foo(true,0.1)
foo(0.9,0.1)

IRTools.IR(typeof(foo), Any, Any) 

##################

using IRTools: blocks, block!, canbranch, IR, argument!, return!, xcall, func, isconditional, Branch

function transform(ir)
    # point each conditional `br`` to its polymorphism block
    @show ir
    for i in eachindex(blocks(ir))
        block = IRTools.block(ir,i)
        polybrs = Branch[]
        branches = IRTools.branches(block) 

        # which variables are relevant to the remainder of the computation?
        args = [Set{IRTools.Variable}() for _ in 1:length(branches)]

        @show i
        for j in length(branches):-1:1
            br = branches[j]    
            if isconditional(br) && br.condition isa IRTools.Variable
                push!(args[j], br.condition)
            end
            for x in br.args 
                if x  isa IRTools.Variable
                    push!(args[j],x)
                end
            end
            if j < length(branches)
                union!(args[j], args[j+1])
            end
            @show args
        end

        for j in 1:length(branches)
            br = branches[j]            
            !isconditional(br) && continue


            # add a polymorphism block to escape to when guard is non-boolean
            poly = block!(ir)
            polycond = argument!(poly)
            handler1 = gensym("polybrhandler")
            handler2 = gensym("polybrhandler")
            poly1 = push!(poly, xcall(handler1, polycond))
            poly2 = push!(poly, xcall(handler2, polycond))
            poly3 = push!(poly, xcall(:ifelse, polycond, poly1, poly2))
            return!(poly, poly3)
            
            # test whether guard is Bool, else go to polymorphism block
            cond = br.condition
            isbool = push!(block, xcall(:isa, cond, :Bool))
            polybr = Branch(isbool, length(blocks(ir)), [cond])
            push!(polybrs, polybr)
        end
        prepend!(branches, polybrs) 
    end
    ir
end

tir = transform(IR(typeof(foo), Any))

f = func(tir)
f(nothing, false)
f(nothing, 0.4)
