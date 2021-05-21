using CUDD

function compile(p::DiceProgram)
    mgr = initialize_cudd()
    compile(mgr, p.expr)
end


function compile(mgr, b::Bool)
    if b
        true_node(mgr)
    else
        false_node(mgr)
    end
end

struct CompiledInt
    bits::Tuple
end

function compile(mgr, i::Int)
    @assert i >= 0
    num_bits = ceil(Int,log2(i+1))
    bits = Vector{Any}(undef, num_bits)
    for bit_idx = 1:num_bits
        b::Bool = i & 1
        @inbounds bits[bit_idx] = compile(mgr, b) 
        i = i >> 1
    end
    CompiledInt(Tuple(bits))
end

true_node(mgr) = Cudd_ReadOne(mgr)
false_node(mgr) = Cudd_ReadLogicZero(mgr)