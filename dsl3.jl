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

function mapvars(block)
    vmap = Dict()
    callerargs = []
    lookup(x) = get!(vmap, x) do 
        if (x isa IRTools.Variable) 
            push!(callerargs, x) # add to block argument list
            argument!(block)
        else
            x # copy constants
        end
    end 
    callerargs, lookup
end

function transform(ir)
    # ensure all cross-block variable use is through block arguments (make blocks functional)
    ir = IRTools.expand!(ir)
    # point each conditional `br`` to its polymorphism block
    for i in eachindex(blocks(ir))
        block = IRTools.block(ir,i)
        branches = IRTools.branches(block) 

        # which variables are relevant to the remainder of the computation?
        args = [Set{IRTools.Variable}() for _ in 1:length(branches)]

        branches_rev = Branch[]
        for j in length(branches):-1:1
            # visit branches in reverse for data flow analysis and inserting branches
            br = branches[j]    
            push!(branches_rev, br)
        
            if isconditional(br) 
                @assert j < length(branches)
                cond = br.condition

                @assert cond isa IRTools.Variable # not sure if this will always be the case... (if false?)

                # add a polymorphism block to escape to when guard is non-boolean
                poly = block!(ir)

                # add arguments for guard, and variables that both branches depend on
                polyargs, lookup = mapvars(poly) 
                next_args_ord = collect(args[j+1])
                
                args_then = map(lookup, br.args)
                f_then = gensym("poly_br_then")
                call_then = push!(poly, xcall(f_then, args_then...))

                else_args = map(lookup, next_args_ord)                
                f_else = gensym("poly_br_else")
                call_else = push!(poly, xcall(f_else, else_args...))
                
                ite = push!(poly, xcall(:ifelse, lookup(cond), call_then, call_else))
                return!(poly, ite)
                
                # test whether guard is Bool, else go to polymorphism block
                isbool = push!(block, xcall(:isa, cond, :Bool))
                polybr = Branch(isbool, length(blocks(ir)), polyargs)
                push!(branches_rev, polybr)

                # data flow for condition 
                push!(args[j], br.condition)
            end

            # data flow for branch arguments
            for x in br.args 
                if x isa IRTools.Variable
                    push!(args[j],x)
                end
            end
            # make data flow cumulative
            if j < length(branches)
                union!(args[j], args[j+1])
            end
        end
        empty!(branches)
        append!(branches, reverse!(branches_rev))
    end
    ir
end

tir = transform(IR(typeof(foo), Any, Any))

f = func(tir)
f(nothing, false, 0.1)
f(nothing, 0.4,0.1)
