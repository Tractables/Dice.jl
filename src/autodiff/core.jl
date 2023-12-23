export value, compute, differentiate, value, Valuation, Derivs, compute_one

using DirectedAcyclicGraphs
using DataStructures: DefaultDict

Valuation = Dict{Var, ADNodeCompatible}
Derivs = Dict{ADNode, ADNodeCompatible}

function compute_one(root, vals::Dict{ADNode, <:ADNodeCompatible})
    foldup(root, compute_leaf, compute_inner, ADNodeCompatible, vals)
end

function compute(var_vals::Valuation, roots)
    vals = Dict{ADNode, ADNodeCompatible}()
    merge!(vals, var_vals)
    for root in roots
        compute_one(root, vals)
    end
    vals
end

function differentiate(var_vals::Valuation, root_derivs::Derivs)
    vals = compute(var_vals, keys(root_derivs))
    derivs = Dict{ADNode, ADNodeCompatible}()
    merge!(derivs, root_derivs)
    foreach_down(keys(root_derivs)) do n
        haskey(derivs, n) && backward(n, vals, derivs)
    end
    vals, derivs
end

# Extending DirectedAcyclicGraphs.jl
function foreach_down(f::Function, roots)
    seen = Set()
    rev_topo = []
    function visit(n)
        n ∈ seen && return
        push!(seen, n)
        if isinner(n)
            for child in children(n)
                visit(child)
            end
        end
        push!(rev_topo, n)
    end
    for root in roots
        visit(root)
    end

    for n in Iterators.reverse(rev_topo)
        f(n)
    end
end
