# Dist with error

export DWE

struct DWE{T} <: Any where T <: Dist
    d::T
    err::DistBool
end

DWE(d::T) where T <: Dist = DWE{T}(d, DistBool(false))

function infer(d::DWE; flip_order=nothing, flip_order_reverse=false)
    mgr, compiler = dist_to_mgr_and_compiler(d; flip_order=flip_order, flip_order_reverse=flip_order_reverse)
    inferer = x -> infer_bool(mgr, compiler(x))
    infer(inferer, d)
end

function infer(inferer, d::DWE)
    ans = Dict()
    error_p = [0.]
    group_infer(inferer, d.err, true, 1.0) do error, error_prior, error_p_
        if error
            # Hack to assign out of scope, there must a better way...
            error_p[1] = error_p_
            return
        end
        group_infer(inferer, d.d, error_prior, error_p_) do assignment, _, p
            if haskey(ans, assignment)
                # If this prints, some group_infer implementation is probably inefficent.
                println("Warning: Multiple paths to same assignment.")
                ans[assignment] += p
            else
                ans[assignment] = p
            end
        end
    end
    ans, error_p[1]
end

function infer_bool(d::DWE{DistBool})
    dist, error_p = infer(d)
    dist[true], error_p
end

function infer_with_observation(d::DWE, observation::DistBool)
    mgr, compiler = dist_to_mgr_and_compiler([d, observation])
    inferer = x -> infer_bool(mgr, compiler(x))
    infer_with_observation(inferer, d, observation)
end

function infer_with_observation(inferer, d::DWE, observation::DistBool)
    ans = Dict()
    error_p = [0.]
    group_infer(inferer, observation, true, 1.0) do observation_met, observe_prior, denom
        if !observation_met return end
        group_infer(inferer, d.err, observe_prior, denom) do error, error_prior, error_p_
            if error
                # Hack to assign out of scope, there must a better way...
                error_p[1] = error_p_/denom
                return
            end
            group_infer(inferer, d.d, error_prior, error_p_) do assignment, _, p
                if haskey(ans, assignment)
                    # If this prints, some group_infer implementation is probably inefficent.
                    println("Warning: Multiple paths to same assignment.")
                    ans[assignment] += p/denom
                else
                    ans[assignment] = p/denom
                end
            end
        end
    end
    ans, error_p[1]
end

# Check if output is a Tuple{Dist, DistBool}; include DistBool in error if so
function dwe_wrap(x, err)
    if x isa Tuple{Dist, DistBool}
        DWE(x[1], x[2] | err)
    else
        DWE(x, err)
    end
end

# Three-operand operations
prob_setindex(x::DWE, y::DWE, z::DWE) = dwe_wrap(prob_setindex(x.d, y.d, z.d), x.err | y.err | z.err)

function ifelse(cond::DWE, then::DWE, elze::DWE)
    d = ifelse(cond.d, then.d, elze.d)
    err = cond.err | ifelse(cond.d, then.err, elze.err)
    DWE(d, err)
end

# Allow promotion to DWE
for op in (:ifelse, :prob_setindex)
    eval(quote
        $op(x::DWE, y::Dist, z::Dist) = $op(x, DWE(y), DWE(z))
        $op(x::Dist, y::DWE, z::Dist) = $op(DWE(x), y, DWE(z))
        $op(x::Dist, y::Dist, z::DWE) = $op(DWE(x), DWE(y), z)
        $op(x::DWE, y::DWE, z::Dist) = $op(x, y, DWE(z))
        $op(x::DWE, y::Dist, z::DWE) = $op(x, DWE(y), z)
        $op(x::Dist, y::DWE, z::DWE) = $op(DWE(x), y, z)
    end)
end

# Binary operations
for op in (:(Base.:+), :(Base.:-), :(Base.:*), :(Base.:/), :(Base.:%),
        :(Base.:&), :(Base.:|), :(Base.:>), :(Base.:<), :(Base.getindex), 
        :prob_equals, :prob_append, :prob_extend, :prob_append_child, 
        :prob_extend_children)
    eval(quote
        $op(x::DWE, y::DWE) = dwe_wrap($op(x.d, y.d), x.err | y.err)
        # Allow promotion to DWE
        $op(x::Dist, y::DWE) = $op(DWE(x), y)
        $op(x::DWE, y::Dist) = $op(x, DWE(y))
    end)
end

# Unary operations
Base.:!(x::DWE) = dwe_wrap(!x.d, x.err)
leaves(x::DWE) = dwe_wrap(leaves(x.d), x.err)

bools(x::DWE) = vcat(bools(x.d), bools(x.err))
