using Alea
using Plots

# Generating .dot files
scale = 0.5
W = 8
F = 4
start = -7.0625
mu = -3.0625
beta2 = 1/scale

e2 = exponential(DistFix{W, F}, beta2, 0.0, 2.0)
dump_dot(e2, filename="mini-experiments/expo_dot/laplace.dot")

t = pr(e2)
plot(t)

x = (@alea unit_gamma(DistFix{7, 6}, 2, -2.0, constants = []))
a = x.returnvalue
b = reduce(&, x.observations)

num_nodes(a)
num_nodes(b)

dump_dot(b, filename="mini-experiments/expo_dot/observations.dot")
dump_dot(a, filename="mini-experiments/expo_dot/lsb_obs.dot")


#shift point gamma
x = (@alea shift_point_gamma(DistFix{5, 4}, 2, -2.0))
a = x.returnvalue
b = x.observations

dump_dot(b, filename="mini-experiments/expo_dot/observations.dot")
dump_dot(a, filename="mini-experiments/expo_dot/lsb_obs.dot")

