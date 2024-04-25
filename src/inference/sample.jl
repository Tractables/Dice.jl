export sample, sample_as_dist, support_as_dist
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

function support_as_dist(x; evidence=true)
    vcache = Dict()
    function call_with(f, key, val)
        vcache[key] = val
        f(val)
        pop!(vcache, key)
    end

    # Call f with every value that x can take given existing assignments in
    # vcache. When f(x_val) is called, frombits_as_dist(x, vcache) == x_val
    function helper(f, n::Bool)
        f(n)
    end
    function helper(f, n::Flip)
        if haskey(vcache, n)
            f(vcache[n])
        else
            call_with(f, n, false)
            call_with(f, n, true)
        end
    end
    function helper(f, n::DistAnd)
        if haskey(vcache, n)
            f(vcache[n])
        else
            helper(n.x) do x
                helper(n.y) do y
                    call_with(f, n, x && y)
                end
            end
        end
    end
    function helper(f, n::DistOr)
        if haskey(vcache, n)
            f(vcache[n])
        else
            helper(n.x) do x
                helper(n.y) do y
                    call_with(f, n, x || y)
                end
            end
        end
    end
    function helper(f, n::DistNot)
        if haskey(vcache, n)
            f(vcache[n])
        else
            helper(n.x) do x
                call_with(f, n, !x)
            end
        end
    end
    function hv(f, v::Vector)
        function hv_helper(i)
        	if i > length(v)
                f()
            else
        	    helper(v[i]) do x
                    hv_helper(i+1)
        		end
        	end
        end
        hv_helper(1)
    end
    		
    res = []
    helper(evidence) do evidence
        if evidence
            bits = tobits(x)
            hv(tobits(x)) do
                push!(res, frombits_as_dist(x, vcache))
            end
        end
    end
    res
end
