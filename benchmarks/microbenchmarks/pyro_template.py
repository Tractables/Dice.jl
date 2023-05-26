import torch
import pyro
import pyro.distributions as dist
import math
import sys

assert len(sys.argv) == 2
num_bits = int(sys.argv[1])

def guide(**kwargs):
    pass

#~begin less
@pyro.infer.config_enumerate
def less_than_model(num_bits):
    a = pyro.sample('a', dist.Categorical(torch.ones(2 ** num_bits)))
    b = pyro.sample('b', dist.Categorical(torch.ones(2 ** num_bits)))
    res = dist.Bernoulli((a < b) * 1.0)
    pyro.sample(None, res, obs=torch.tensor(1.))

elbo = pyro.infer.TraceEnum_ELBO(max_plate_nesting=0)
p_z = pyro.do(less_than_model, data={})
pr = math.exp(-elbo.loss(p_z, guide, num_bits=num_bits))
print(pr)
#~end

#~begin equals
@pyro.infer.config_enumerate
def equals_model(num_bits):
    a = pyro.sample('a', dist.Categorical(torch.ones(2 ** num_bits)))
    b = pyro.sample('b', dist.Categorical(torch.ones(2 ** num_bits)))
    res = dist.Bernoulli((a == b) * 1.0)
    pyro.sample(None, res, obs=torch.tensor(1.))

elbo = pyro.infer.TraceEnum_ELBO(max_plate_nesting=0)
p_z = pyro.do(equals_model, data={})
pr = math.exp(-elbo.loss(p_z, guide, num_bits=num_bits))
print(pr)
#~end

#~begin sum
@pyro.infer.config_enumerate
def sum_model(num_bits, bit_of_interest):
    a = pyro.sample('a', dist.Categorical(torch.ones(2 ** num_bits)))
    b = pyro.sample('b', dist.Categorical(torch.ones(2 ** num_bits)))
    res = dist.Bernoulli((((a + b) >> bit_of_interest) & 1) * 1.0)
    pyro.sample(None, res, obs=torch.tensor(1.))

pr = None
for bit_of_interest in range(num_bits + 1):
    elbo = pyro.infer.TraceEnum_ELBO(max_plate_nesting=0)
    p_z = pyro.do(sum_model, data={})
    pr = math.exp(-elbo.loss(p_z, guide, num_bits=num_bits,
                    bit_of_interest=bit_of_interest))
print(pr)
#~end
