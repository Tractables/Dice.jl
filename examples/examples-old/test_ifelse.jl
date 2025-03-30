using Alea
using Alea: ifelse

cg = @alea_ite begin
    b = DistInt([DistBool(false)])
    ifelse(flip(0.5), b, b)
end

@assert length(cg.bits) > 0
infer(cg)
