export sample, sample_as_dist
using DirectedAcyclicGraphs: foldup
using Distributions

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

softmax2(a) = [
    exp(a[1]) / (exp(a[1]) + exp(a[2])),
    exp(a[2]) / (exp(a[1]) + exp(a[2]))
]
function gumbel_softmax(rng, p, temperature)
    y = softmax2([
        (log(1-p)+rand(rng, Gumbel(0, 1))) / temperature,
        (log(p)+rand(rng, Gumbel(0, 1))) / temperature,
    ])
    y[2]
end

function sample_as_dist(rng, x; evidence=true, temperature)
    while true
        vcache = Dict()
        fl(n::Flip) = begin
            if !haskey(vcache, n)
                vcache[n] = flip(gumbel_softmax(rng, n.prob, temperature))
            end
            vcache[n]
        end

        fi(n::DistAnd, call) = begin
            if !haskey(vcache, n)
                vcache[n] = call(n.x) & call(n.y)
            end
            vcache[n]
        end

        fi(n::DistOr, call) = begin
            if !haskey(vcache, n)
                vcache[n] = call(n.x) | call(n.y)
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
            foldup(bit, fl, fi, AnyBool)
        end
        return frombits_as_dist(x, vcache)
    end
end
