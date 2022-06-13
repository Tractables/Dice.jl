using Dice

# + that returns a Tuple{DistInt, DistBool}
cg = @dice begin
    x = if DWE(flip(0.3)) 
        DWE(DistInt(0))
    else
        DWE(DistInt(1))
    end
    x + DWE(DistInt(3))
end

dist, err = infer(cg)
@assert err ≈ 0.7
@assert dist[3] ≈ 0.3
@assert length(dist) == 1


# + that returns a DistString
cg = @dice begin
    DWE(DistString("abc")) + DWE(DistChar('d'))
end
dist, err = infer(cg)
@assert err == 0
@assert dist["abcd"] ≈ 1
@assert length(dist) == 1

cg = @dice begin
    DWE(DistString("abc"))[DWE(if flip(.4) DistInt(2) else DistInt(100) end)]
end
dist, err = infer(cg)
@assert err ≈ 0.6
@assert dist['b'] ≈ 0.4
@assert length(dist) == 1

# Test automatic conversion
cg = @dice begin
    if flip(true)
        DWE(DistInt(1)) + DistInt(0)
    else
        DistInt(7)
    end
end
dist, err = infer(cg)
@assert err == 0
@assert dist[1] ≈ 1
@assert length(dist) == 1
