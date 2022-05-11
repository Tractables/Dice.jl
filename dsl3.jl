using IRTools, IfElse

##################
# Motivation
##################

function foo(x,y)
    z = y*0.5
    if x
        0.4 + z
    else
        0.1 + z
    end
end

# control flow depending on `Bool`` guards works by default
foo(true,0.1) # 0.45

# we would like control flow to be polymorphic, 
# for example to let `AbstractFloat` guards take the weighted average of both branches
IfElse.ifelse(g::AbstractFloat, t, e) = g*t + (1-g)*e

# control flow depending on such `AbstractFloat` guards is not polymorphic by default
foo(0.9,0.1) # ERROR: TypeError: non-boolean (Float64) used in boolean context

##################
# Implementation
##################

using IRTools: blocks, block!, canbranch, IR, argument!, return!, xcall, func, isconditional, Branch, arguments

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
    helpers = []
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
                
                # look up all possible arguments for poly block
                lookup(cond) # guard is first argument
                foreach(lookup, br.args)
                foreach(lookup, args[j+1])                
                
                helper = gensym("polybr_help")
                push!(helpers, (helper, copy(branches_rev), lookup, arguments(poly)))

                branchargs = @view arguments(poly)[2:end]
                call_then = push!(poly, xcall(Base.invokelatest, helper, true, branchargs...))
                call_else = push!(poly, xcall(Base.invokelatest, helper, false, branchargs...))
                ite = push!(poly, xcall(IfElse.ifelse, lookup(cond), call_then, call_else))
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

    # generate helper ir
    helpers_ir = map(helpers) do helper 
        sym, branches_rev, lookup1, caller_args = helper

        # add new block at the top
        help_ir = copy(ir)
        header = block!(help_ir, 1)

        # introduce header arguments for each caller argument
        _, lookup2 = mapvars(header) 
        foreach(lookup2, caller_args)
        lookup(x) = lookup2(lookup1(x))

        # add branch statements translated to new variable vocabulary
        branches = IRTools.branches(header) 
        for i=length(branches_rev):-1:1
            br = branches_rev[i]
            br2 = Branch(lookup(br.condition), br.block+1, map(lookup, br.args))
            push!(branches, br2)
        end
        sym, help_ir
    end 


    ir, helpers_ir
end

function gen_poly_f(funtype, args...)
    ir = IR(funtype, args...)
    fir, helpers = transform(ir)
    for (helpername, helperir) in helpers
        # cf https://github.com/FluxML/IRTools.jl/blob/master/src/eval.jl
        @eval @generated function $(helpername)($([Symbol(:arg, i) for i = 1:length(arguments(helperir))]...))
            # println("called helper")
            return IRTools.Inner.build_codeinfo($helperir)
            # return 0.5
        end
    end
    @eval @generated function $(gensym("polybr"))($([Symbol(:arg, i) for i = 1:length(arguments(fir))]...))
        return IRTools.Inner.build_codeinfo($fir)
    end
end

##################
# Example
##################

foo2 = gen_poly_f(typeof(foo), Any, Any)

foo2(nothing, true, 0.1) # 0.45
foo2(nothing, 0.4, 0.1) #0.27