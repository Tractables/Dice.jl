using Dice 
using Dice: Flip, ifelse, num_ir_nodes
# @show localARGS
i = 3#parse(Int64, localARGS[1])

# x =  @benchmark begin 
code = @dice begin   
    a = uniform(DistUInt{i+1}, i) + DistUInt{i+1}(1)
    b = uniform(DistUInt{i+1}, i) + DistUInt{i+1}(1)
    for _ = 1 : 1 + (i+1) ÷ log2(MathConstants.golden)
        t = b
        converged = prob_equals(b, DistUInt{i+1}(0))
        amb = (a % b)
        b = ifelse(converged, b, amb)
        a = ifelse(converged, a, t)
    end
    gcd=a
    # prob_equals(g, DistUInt{i+1}(1))
    gcd
end

x= code
using CUDD
debug_info_ref = Ref{CuddDebugInfo}()
pr(x, algo=Cudd(CUDD.CUDD_REORDER_NONE, debug_info_ref), ignore_errors=true)
println(debug_info_ref[].num_nodes)

pr(x, algo=Cudd(CUDD.CUDD_REORDER_SIFT, debug_info_ref), ignore_errors=true)
println(debug_info_ref[].num_nodes)