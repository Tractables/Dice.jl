using IRTools

##################

function foo(x)
    if x
        0.4
    else
        0.1
    end
end

ifelse(g::AbstractFloat, t, e) = g*t + (1-g)*e

foo(true)
foo(0.9)

@code_ir foo(0.9) 

##################

using IRTools: blocks, block!, canbranch, IR, argument!, return!, xcall, func, branches, isconditional, Branch

function transform(ir)
    # point each conditional `br`` to its polymorphism block
    for block in blocks(ir)
        for br in copy(branches(block)) 
            !isconditional(br) && continue
            @show br

            # add a polymorphism block to escape to when guard is non-boolean
            poly = block!(ir)
            polycond = argument!(poly)
            poly1 = push!(poly, xcall(:error, "control flow polymorphism not yet implemented"))
            return!(poly, poly1)
            
            # test whether guard is Bool, else go to polymorphism block
            cond = br.condition
            @show cond
            isbool = push!(block, xcall(:isa, cond, :Bool))
            brpoly = Branch(isbool, 3, [cond])
            pushfirst!(branches(block), brpoly) 
        end
    end
    ir
end

tir = transform(IR(typeof(foo), Any))

f = func(tir)
f(nothing, false)
f(nothing, 0.4)
