using Alea
using Alea: ifelse

function bwh_discrete(p::Vector{Float64})
    @assert ispow2(length(p)) "Distribution length should be power of 2"
    prefix_sums = accumulate(+, p)
    @assert last(prefix_sums) ≈ 1 "Distribution should sum to 1"
    function helper(i, j)
        if i == j
            DistInt(i - 1)
        else
            first_half_end = (i + j - 1) ÷ 2
            first_half_p = prefix_sums[first_half_end] - prefix_sums[i] + p[i]
            total_p = prefix_sums[j] - prefix_sums[i] + p[i]
            ifelse(flip(first_half_p/total_p),
                helper(i, first_half_end),
                helper(first_half_end+1, j))
        end
    end
    helper(1, length(p))
end

bwh_discrete32 = bwh_discrete([1/32 for _ in 0:31])
# hoist(bwh_discrete32)