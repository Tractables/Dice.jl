using Revise
using MLDatasets: MNIST
using Dice
using Random

function matrix_var!(name, init)
    # TODO: Add matrix primitives in autodiff
    m = Matrix{Dice.ADNode}(undef, size(init))
    for i in CartesianIndices(init)
        var_name = "$(name)[$(join(Tuple(i), ','))]"
        m[i] = var!(var_name, init[i])
    end
    m
end

HIDDEN_LAYER_SIZE = 256
TRAIN_ROWS = 1000

Random.seed!(0)
θ1_init = rand(28 * 28, HIDDEN_LAYER_SIZE)
θ2_init = rand(HIDDEN_LAYER_SIZE, 10)

clear_vars!()
θ1 = matrix_var!("θ1", θ1_init)
θ2 = matrix_var!("θ2", θ2_init)

Dice._variable_to_value

x = reshape(MNIST(:train).features, (28 * 28, 60000)) |> transpose
x = x[1:TRAIN_ROWS, :]

t1 = @elapsed x * θ1_init
# 0.008783958
t2 = @elapsed x * θ1
# 70.553411583
(typeof(θ1))
function Base.:(*)(M1::AbstractMatrix, M2::)

* θ2

matrix_param("", (2, 3), 0)
M
rand(256, 28 * 28) * x
map(Dice.sigmoid, x)