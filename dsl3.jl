using IRTools, IfElse

##################
# Motivation
##################

# a function with control flow
function foo(x,y)
    z = y*0.5
    if x
        0.4 + z
    else
        0.1 + z
    end
end

# control flow depending on `Bool`` guards works by default
foo(true, 0.1) # 0.45

# we would like control flow to be polymorphic, 
# for example to let `AbstractFloat` guards take the weighted average of both branches
IfElse.ifelse(guard::AbstractFloat, then, elze) = guard*then + (1-guard)*elze

# control flow depending on such `AbstractFloat` guards is not polymorphic by default
foo(0.9, 0.1) # ERROR: TypeError: non-boolean (Float64) used in boolean context

##################
# Implementation
##################

using IRTools: blocks, block!, IR, argument!, return!, xcall, isconditional, Branch, arguments

"Utility to translate between caller and function/block argument lists"
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

"Transform IR to have polymorphic control flow and add helper function IR"
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
                
                # put a new helper function on the TODO list for later
                helper = gensym("polybr_help")
                push!(helpers, (helper, copy(branches_rev), lookup, arguments(poly)))

                # call helper function for each branch, return polymorphic IfElse value
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

"Generate a version of the method that has polymorphic control flow"
function gen_poly_f(funtype, args...)
    ir = IR(funtype, args...)
    fir, helpers = transform(ir)
    for (helpername, helperir) in helpers
        # cf https://github.com/FluxML/IRTools.jl/blob/master/src/eval.jl
        @eval @generated function $(helpername)($([Symbol(:arg, i) for i = 1:length(arguments(helperir))]...))
            return IRTools.Inner.build_codeinfo($helperir)
        end
    end
    polybr = @eval @generated function $(gensym("polybr"))($([Symbol(:arg, i) for i = 1:length(arguments(fir))]...))
        return IRTools.Inner.build_codeinfo($fir)
    end
    # hide first argument
    return (args...) -> polybr(nothing, args...)
end

##################
# Example
##################

# apply source transformation
foo2 = gen_poly_f(typeof(foo), Any, Any)

# `Bool` guards still work (and evaluate only a single branch)
foo2(true, 0.1) # 0.45

# `AbstractFloat`` guards now also work
foo2(0.4, 0.1) #0.27

# if the compiler can prove that the guard is `Bool`, the additional code disappears
@code_typed foo2(true, 0.1)

# if the compiler can prove that the guard is not `Bool``, 
# there is no traditional control flow, 
# only calls to helper functions for both branches and `ifelse`
@code_typed foo2(0.4, 0.1)