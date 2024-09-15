using Revise
using Dice
using ADEV
using Infiltrator
using ForwardDiff
using Random
using StatsBase: mean, std
using ReverseDiff

function mk_adev_prog(fl)
    function (theta)
        @adev begin
            # let x = @sample(fl(theta[1])) & @sample(fl(theta[1])) & !@sample(fl(theta[1])),
            #     y = @sample(fl(theta[2])) & !@sample(fl(theta[2])) & !@sample(fl(theta[2]))
            #     x & y
            # end
            @sample(fl(theta[1])) & @sample(fl(theta[1])) & !@sample(fl(theta[1])) & @sample(fl(theta[2])) & !@sample(fl(theta[2])) & !@sample(fl(theta[2]))
        end
    end
end

adev_prog = mk_adev_prog(flip_reinforce)
dual_val = [ ForwardDiff.Dual(v, 1) for v in val ]
N = 100
approximate(f, N) = sum([f() for _ in 1:N]) / N

reverse_mode_grad() = ReverseDiff.gradient(
    (val) -> adev_prog(val)(r -> (wants_grad, rng) -> r)(true, Random.Xoshiro()),
    val
)
forward_mode_grad() = ForwardDiff.gradient(
    (val) -> adev_prog(val)(r -> (wants_grad, rng) -> r)(true, Random.Xoshiro()),
    val
)


val = [0.5, 0.5]
@time for _ in 1:1000
    val += 0.01 * approximate(forward_mode_grad, N)
end
val

val = [0.5, 0.5]
@time for _ in 1:1000
    val += 0.01 * approximate(reverse_mode_grad, N)
end
val

# why does this only give a single dual?
adev_prog(dual_val)(r -> (wants_grad, rng) -> r)(true, Random.Xoshiro())