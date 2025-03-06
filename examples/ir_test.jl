using Revise
using Dice 
using IRTools
using IRTools: @dynamo, IR, recurse!, self, xcall, functional, var

function f(x)
    x * x + 1
end
ir = @code_ir f(2)

ir[var(4)] = xcall(:-, var(3), 1)
@code_ir f(2)

f_mod = IRTools.func(ir)




function idk()
    a = 4
    b = 3
    c = a+b
    return c
end
@code_ir idk()

function dice_func()
    @dice begin
        a = uniform(DistUInt{3}, 2)
        b = uniform(DistUInt{3}, 2)
        c = a+b
        c
    end
end


@code_ir dice_func()