using Dice

scale = 0.5
W = 8
F = 4
start = -7.0625
mu = -3.0625
beta2 = 1/scale
e2 = exponential(DistFix{W, F}, beta2, start, mu)
dump_dot(e2, filename="laplace.dot")

t = pr(e2)
plot(t)

x = (@dice unit_gamma(DistFix{5, 4}, 2, -2.0, constants = [], constant_flips=[], f = []))
a = x.returnvalue

b = reduce(&, x.observations)

dump_dot(b, filename="observations.dot")

dump_dot(a, filename="lsb_obs.dot")


#shift point gamma
x = (@dice shift_point_gamma(DistFix{5, 4}, 2, -2.0))
a = x.returnvalue

b = x.observations

dump_dot(b, filename="observations.dot")

dump_dot(a, filename="lsb_obs.dot")

