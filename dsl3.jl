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

# function foo(x,y)
#     if x
#         0.4  + y
#     else
#         0.1  +y
#     end
# end

ifelse(g::AbstractFloat, t, e) = g*t + (1-g)*e

foo(true,0.1)
foo(0.9,0.1)

IRTools.IR(typeof(foo), Any, Any; slots = false)
IRTools.expand!(IRTools.IR(typeof(foo), Any, Any; slots = false))

##################

using IRTools: blocks, block!, canbranch, IR, argument!, return!, xcall, func, isconditional, Branch

function transform(ir)
    # ensure all cross-block variable use is through block arguments (make blocks functional)
    ir = IRTools.expand!(ir)
    # point each conditional `br`` to its polymorphism block
    @show ir
    for i in eachindex(blocks(ir))
        block = IRTools.block(ir,i)
        branches = IRTools.branches(block) 

        # which variables are relevant to the remainder of the computation?
        args = [Set{IRTools.Variable}() for _ in 1:length(branches)]

        branches_rev = Branch[]
        @show i
        for j in length(branches):-1:1
            # visit branches in reverse for data flow analysis and inserting branches
            br = branches[j]    
            push!(branches_rev, br)
            @show j, br
            
            # collect variables that branch depends on
            for x in br.args 
                if x isa IRTools.Variable
                    push!(args[j],x)
                end
            end

            if isconditional(br) 
                # collect variable that branch condition depends on
                cond = br.condition
                (cond isa IRTools.Variable) && push!(args[j], br.condition)

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
                isbool = push!(block, xcall(:isa, cond, :Bool))
                polybr = Branch(isbool, length(blocks(ir)), [cond])
                push!(branches_rev, polybr)

                # cumulative data flow
                if j < length(branches)
                    union!(args[j], args[j+1])
                end
            end
            @show args
        end
        empty!(branches)
        append!(branches, reverse!(branches_rev))
    end
    ir
end

tir = transform(IR(typeof(foo), Any, Any))

f = func(tir)
f(nothing, false,0.1)
f(nothing, 0.4,0.1)
