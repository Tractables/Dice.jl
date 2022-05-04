using IRTools

function foo(x)
    if x
        0.4
    else
        0.1
    end
end

foo(true)
foo(0.9)

@code_ir foo(0.9) 

##################

ifelse(g::AbstractFloat, t, e) = g*t + (1-g)*e

function bar(x)
    if x isa Bool
        if x
            0.4
        else
            0.1
        end
    else
        ifelse(x, 0.4, 0.1)
    end
end

bar(true)
bar(0.9)

@code_ir bar(0.9) 

##################

ir = @code_ir foo(0.9) 

using IRTools: blocks, block!

function transform(ir)
    @assert length(blocks(ir)) == 2
    @assert !any(canbranch,blocks(ir))

    block!(ir)
    ir
end

transform(@code_ir foo(0.9))
