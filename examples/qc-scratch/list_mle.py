import torch
import numpy as np
from torch.autograd import Variable


lengths_np = np.array([0, 2, 4, 6,  8])
lengths = Variable(torch.from_numpy(lengths_np).long())
p = Variable(torch.rand(1), requires_grad=True)

learning_rate = 0.0001
for t in range(1000):
    # log-likelihoods
    lls = (
        torch.log(p).repeat(lengths.shape)
        + lengths * torch.log(torch.ones(1) - p)
    )

    # negative log-likelihood
    nll = -torch.sum(lls)
    nll.backward()

    p.data -= learning_rate * p.grad.data
    p.grad.data.zero_()
print(p)


learning_rate = 0.0001
size0 = 8


ps = Variable(torch.rand(size0 + 1), requires_grad=True)
vars = [ps]

for t in range(5000):
    x = torch.arange(size0 + 1).repeat((lengths.shape[0], 1)).T

    mask = x >= lengths
    y = torch.log(1 - ps[size0 - x])
    y[mask] = 0

    nll = -torch.sum(y) - torch.sum(torch.log(ps[size0 - lengths]))
    nll.backward()

    for var in vars:
        var.data -= learning_rate * var.grad.data
        var.grad.data.zero_()
print(vars)


size0 = 3


# learning_rate = 0.0001
# size0 = 8

# w_nil = Variable(torch.rand(1), requires_grad=True)
# b_nil = Variable(torch.rand(1), requires_grad=True)
# w_cons = Variable(torch.rand(1), requires_grad=True)
# b_cons = Variable(torch.rand(1), requires_grad=True)

# vars = [w_cons, b_nil, w_cons, b_cons]

# print(vars)
# for t in range(1):
#     x = torch.arange(size0 + 1).repeat((lengths.shape[0], 1)).T
#     mask = x >= lengths
#     ps = (torch.arange(size0 + 1) * w_nil + b_nil) / (torch.arange(size0 + 1) * (w_nil + w_cons) + b_nil + b_cons)
#     # ps = 1 / (torch.arange(size0 + 1) * w_cons + 1)
#     print(ps)
#     y = torch.log(1 - ps[size0 - x])
#     y[mask] = 0
#     nll = -torch.sum(y) - torch.sum(torch.log(ps[size0 - lengths]))
#     print(nll)

#     nll.backward()

#     for var in vars:
#         var.data -= learning_rate * var.grad.data
#         var.grad.data.zero_()
# print(vars)

# print("loglik  =", nll.data.numpy(), "p =", p.data.numpy(), "dL/dp = ", p.grad.data.numpy())   


# x = (s - (s - l + 1) + 1) * torch.log(1 - p)
# lls -= (s - (s - l + 1) + 1) * torch.log(1 - p)

