# Proof-of-concept of training a network to classify MNIST digits
# It's slow - we should use a 3rd party ML framework instead

# Eventual goal would be to do MNIST-sum, as in
# https://arxiv.org/pdf/1805.10872.pdf

using MLDatasets: MNIST
using Revise
using Dice
using Random

map_sigmoid(x::ADNode) = ad_map(Dice.sigmoid, Dice.deriv_sigmoid, x)

function discrete_weights(::Type{DistUInt{W}}, weights::Vector{<:ADNode}) where W
    res = DistUInt{W}(length(weights) - 1)
    acc = last(weights)
    for i in reverse(1:length(weights) - 1)
        acc += weights[i]
        res = @dice_ite if flip(weights[i] / acc)
            DistUInt{W}(i - 1)
        else
            res
        end
    end
    res
end

HIDDEN_LAYER_SIZE = 100
TRAIN_ROWS = 20

Random.seed!(0)
θ1_init = rand(28 * 28, HIDDEN_LAYER_SIZE)
θ2_init = rand(HIDDEN_LAYER_SIZE, 10)

clear_vars!()
θ1 = new_var!("θ1", θ1_init)
θ2 = new_var!("θ2", θ2_init)

x = reshape(MNIST(:train).features, (28 * 28, 60000)) |> transpose
x = x[1:TRAIN_ROWS, :]
y = MNIST(:train).targets[1:TRAIN_ROWS]

dw = map_sigmoid(map_sigmoid(x * θ1) * θ2)
dw = [dw[i] for i in CartesianIndices((TRAIN_ROWS, 10))]
predictions = [discrete_weights(DistUInt{4}, dw[i, :]) for i in 1:TRAIN_ROWS]
correct = [prob_equals(pred, DistUInt{4}(label)) for (pred, label) in zip(predictions, y)]

pr_corrects = [dist[true] for dist in pr(correct...)]
expected_accuracy = sum(pr_corrects) / length(pr_corrects)
println("Expected accuracy: $(expected_accuracy)")

train_vars!(correct; epochs=1000, learning_rate=0.003)

pr_corrects = [dist[true] for dist in pr(correct...)]
expected_accuracy = sum(pr_corrects) / length(pr_corrects)
println("Trained expected accuracy: $(expected_accuracy)")
