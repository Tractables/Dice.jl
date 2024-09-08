export sample, sample_as_dist, sample_default_rng
using Random
using DirectedAcyclicGraphs: foldup

"""Run vanilla rejection sampling without any compilation"""
function sample(rng, x; evidence=true)
    while true
        vcache = Dict()
        fl(n::Flip) = begin
            if !haskey(vcache, n)
                vcache[n] = rand(rng) < n.prob
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

function sample_default_rng(x; evidence=true)
    sample(Random.default_rng(), x; evidence)
end

function sample_as_dist(rng, a, x; evidence=true)
    while true
        vcache = Dict()
        fl(n::Flip) = begin
            if !haskey(vcache, n)
                p = if n.prob isa ADNode
                    compute(a, n.prob)
                else
                    n.prob
                end
                vcache[n] = rand(rng) < p
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
        return frombits_as_dist(x, vcache)
    end
end

tobits(::Integer) = []
frombits_as_dist(i::Integer, _) = i
prob_equals(x::Integer, y::Integer) = x == y
