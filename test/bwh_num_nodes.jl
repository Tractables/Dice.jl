using Revise
using Dice
using Dice: num_flips, num_nodes, ifelse

# Number of nodes BWH needs to model a distribution on n bits
bwh_num_nodes(n) = 2^(n + 1) - n

function generate_code_bwh(p::Vector{Float64})
    @dice begin
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
end

function test_bwh_num_nodes(p::Vector{Float64})
    cg = generate_code_bwh(p)
    @assert infer_int(cg) ≈ p  # Verify correctness

    nn = num_nodes(cg)
    num_bits = round(Int, log2(length(p)))
    @assert nn == bwh_num_nodes(num_bits)  # Verify num bits

    println("BWH for a $(num_bits)-bit distribution: $(nn) nodes, $(num_flips(cg)) flips")
end

dist_2 = [0.5, 0.5]
dist_4 = [0.1, 0.2, 0.3, 0.4]
dist_8 = [0.02, 0.04, 0.06, 0.08, 0.1, 0.12, 0.14, 0.44]
dist_16 = [0.005, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07, 0.08, 0.09, 0.001, 0.11, 0.12, 0.13, 0.14, 0.022, 0.032]

for dist in [dist_2, dist_4, dist_8, dist_16]
    test_bwh_num_nodes(dist)
end
