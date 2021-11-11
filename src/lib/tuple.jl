
# Tuples

struct ProbTuple <: Dist
    mgr
    left::Dist
    right::Dist
end

function prob_equals(x::ProbTuple, y::ProbTuple)
    if typeof(x.left) != typeof(y.left) || typeof(x.right) != typeof(y.right)
        # better to just define equality between different types to be false by default???
        false_constant(x.mgr)
    else
        # TODO order left and right checks by first fail principle 
        left_eq = prob_equals(x.left, y.left)
        if !issat(left_eq)
            false_constant(x.mgr)
        else
            right_eq = prob_equals(x.right, y.right)
            left_eq & right_eq
        end
    end
end

function ite(cond::DistBool, then::T, elze::T) where {T <: ProbTuple}
    # TODO optimize of deterministic conditions
    left = ite(cond, then.left, elze.left)
    right = ite(cond, then.right, elze.right)
    ProbTuple(cond.mgr, left, right)
end

bools(t::ProbTuple) = [bools(t.left); bools(t.right)]
   