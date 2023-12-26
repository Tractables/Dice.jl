export sample
using DirectedAcyclicGraphs: foldup

"""Run vanilla rejection sampling without any compilation"""
function sample(x; evidence=true)
    vals = Dict{ADNode, Real}()
    while true
        vcache = Dict()
        fl(n::Flip) = begin
            if !haskey(vcache, n)
                p = if n.prob isa ADNode
                    compute(n.prob, vals)
                else
                    n.prob
                end
                vcache[n] = rand() < p
            end
            vcache[n]
        end

        fi(n::DistAnd, call) = begin
            if !haskey(vcache, n)
                vcache[n] = call(n.x) && call(n.y)
            end
            vcache[n]
        end

        fi(n::DistOr, call) = begin
            if !haskey(vcache, n)
                vcache[n] = call(n.x) || call(n.y)
            end
            vcache[n]
        end

        fi(n::DistNot, call) = begin
            if !haskey(vcache, n)
                vcache[n] = !call(n.x)
            end
            vcache[n]
        end

        vcache = Dict()
        evidence_computed = if evidence isa Bool
            evidence
        else
            foldup(evidence, fl, fi, Bool)
        end
        evidence_computed || continue
        for bit in tobits(x)
            bit isa Bool && continue
            foldup(bit, fl, fi, Bool)
        end
        return frombits(x, vcache)
    end
end
