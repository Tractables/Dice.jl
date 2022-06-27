using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function gaussian(p::Int, binbits::Int, b::Bool, b2::Bool, flag::Int)
    code = @dice begin
        t = DistFixParam{binbits+3, binbits}
        d = if flag == 1 Normal(3, 1) elseif flag == 2 Normal(0, 3) else Normal(8, 3) end
        continuous(dicecontext(), p, t, d, b, b2)
    end
    code
end

for i = 0:10
    for j = 0:i+2
        f = gaussian(2^j, i, false, false, 1)
        a = compile(f)
        @show i, j, num_flips(a), num_nodes(a), expectation(a)
    end
end

x = Vector(undef, 5)
y = Vector(undef, 5)
for j = 0:3
    f = gaussian(2^j, 1, false, false, 1)
    a = compile(f)
    x[j+1] = j
    y[j+1] = num_nodes(a)
end
plot(x, y)

bits = 0
pieces = 4
f = gaussian(pieces, bits, false, false, 1)
a = compile(f)
num_nodes(a)
num_flips(a)
infer(a)
dump_dot(a, "gaussian_0_4.dot")

bits = 0
pieces = 2
f = gaussian(pieces, bits, false, false, 1)
a = compile(f)
num_nodes(a)
num_flips(a)
infer(a)
dump_dot(a, "gaussian_0_2.dot")

bits = 3
pieces = 4
f = gaussian(pieces, bits, false, false, 1)
a = compile(f)
num_nodes(a)
num_flips(a)
infer(a)
dump_dot(a, "gaussian_3_4.dot")

function uniform_gaussian(p::Int, binbits::Int, b::Bool, b2::Bool, flag::Int)
    code = @dice begin
        t = DistFixParam{binbits+3, binbits}
        mu = uniform(dicecontext(), 1, t)
        d = if flag == 1 Normal(3, 1) elseif flag == 2 Normal(0, 3) else Normal(8, 3) end
        a = continuous(dicecontext(), p, t, d, b, b2)
        # mu = uniform(dicecontext(), 1, t)
        (a + mu)[1]
    end
    code
end

for i = 0:10
    for j = 0:i+2
        f = uniform_gaussian(2^j, i, false, false, 1)
        a = compile(f)
        @show i, j, num_flips(a), num_nodes(a)
    end
end

function gaussian_uniform(p::Int, binbits::Int, b::Bool, b2::Bool, flag::Int)
    code = @dice begin
        t = DistFixParam{binbits+3, binbits}
        # mu = uniform(dicecontext(), 1, t)
        d = if flag == 1 Normal(3, 1) elseif flag == 2 Normal(0, 3) else Normal(8, 3) end
        a = continuous(dicecontext(), p, t, d, b, b2)
        mu = uniform(dicecontext(), 1, t)
        (a + mu)[1]
    end
    code
end

for i = 0:10
    for j = 0:i+2
        f = gaussian_uniform(2^j, i, false, false, 1)
        a = compile(f)
        @show i, j, num_flips(a), num_nodes(a)
    end
end

function uniform_gaussian_bits(p::Int, binbits::Int, b::Bool, b2::Bool, flag::Int)
    code = @dice begin
        t = DistFixParam{binbits+3, binbits}
        mu = add_bits(uniform(dicecontext(), 1, t), 1)
        d = if flag == 1 Normal(3, 1) elseif flag == 2 Normal(0, 3) else Normal(8, 3) end
        a = add_bits(continuous(dicecontext(), p, t, d, b, b2), 1)
        # mu = uniform(dicecontext(), 1, t)
        (a + mu)[1]
    end
    code
end

for i = 0:10
    for j = 0:i+2
        f = uniform_gaussian_bits(2^j, i, false, false, 1)
        a = compile(f)
        @show i, j, num_flips(a), num_nodes(a)
    end
end

function gaussian_uniform_bits(p::Int, binbits::Int, b::Bool, b2::Bool, flag::Int)
    code = @dice begin
        t = DistFixParam{binbits+3, binbits}
        # mu = uniform(dicecontext(), 1, t)
        d = if flag == 1 Normal(3, 1) elseif flag == 2 Normal(0, 3) else Normal(8, 3) end
        a = add_bits(continuous(dicecontext(), p, t, d, b, b2), 1)
        mu = add_bits(uniform(dicecontext(), 1, t), 1)
        (a + mu)[1]
    end
    code
end

for i = 0:10
    for j = 0:i+2
        f = gaussian_uniform_bits(2^j, i, false, false, 1)
        a = compile(f)
        @show i, j, num_flips(a), num_nodes(a)
    end
end

function gaussian_uniform_eq(p::Int, binbits::Int, b::Bool, b2::Bool, flag::Int)
    code = @dice begin
        t = DistFixParam{binbits+3, binbits}
        d = if flag == 1 Normal(3, 1) elseif flag == 2 Normal(0, 3) else Normal(8, 3) end
        a = add_bits(continuous(dicecontext(), p, t, d, b, b2), 1)
        mu = add_bits(uniform(dicecontext(), binbits+3, t), 1)
        prob_equals((a + mu)[1], DistFixParam{binbits + 4, binbits}(dicecontext(), 2.0))
    end
    code
end

for i = 0:10
    for j = 0:i+2
        f = gaussian_uniform_eq(2^j, i, false, false, 1)
        a = compile(f)
        @show i, j, num_flips(a), num_nodes(a), infer(a)
    end
end

bits = 0
pieces = 1
f = gaussian_uniform_eq(pieces, bits, false, false, 1)
a = compile(f)
num_nodes(a)
num_flips(a)
infer(a)
dump_dot(a, "rough.dot")

bits = 0
pieces = 2
f = gaussian_uniform_eq(pieces, bits, false, false, 1)
a = compile(f)
num_nodes(a)
num_flips(a)
infer(a)
dump_dot(a, "rough2.dot")

bits = 0
pieces = 4
f = gaussian_uniform_eq(pieces, bits, false, false, 1)
a = compile(f)
num_nodes(a)
num_flips(a)
infer(a)
dump_dot(a, "rough3.dot")

 function uniform_gaussian_eq(p::Int, binbits::Int, b::Bool, b2::Bool, flag::Int)
    code = @dice begin
        t = DistFixParam{binbits+3, binbits}
        d = if flag == 1 Normal(3, 1) elseif flag == 2 Normal(0, 3) else Normal(8, 3) end
        mu = uniform(dicecontext(), binbits+3, t)
        a = continuous(dicecontext(), p, t, d, b, b2)
        prob_equals((a + mu)[1], t(dicecontext(), 0.0))
    end
    code
end

for i = 0:10
    for j = 0:i+2
        f = uniform_gaussian_eq(2^j, i, false, false, 1)
        a = compile(f)
        @show i, j, num_flips(a), num_nodes(a)
    end
end

x = Vector(undef, 13)
y = Vector(undef, 13)
for j = 0:12
    f = gaussian_uniform_eq(2^j, 10, false, false, 1)
    a = compile(f)
    x[j+1] = j
    y[j+1] = num_nodes(a)
end
plot(x, y)

bits = 1
pieces = 1
f = gaussian_uniform_eq(pieces, bits, false, false, 1)
a = compile(f)
num_nodes(a)
num_flips(a)
infer(a)
dump_dot(a, "rough.dot")

bits = 1
pieces = 2
f = gaussian_uniform_eq(pieces, bits, false, false, 1)
a = compile(f)
num_nodes(a)
num_flips(a)
infer(a)
dump_dot(a, "rough2.dot")

bits = 1
pieces = 4
f = gaussian_uniform_eq(pieces, bits, false, false, 1)
a = compile(f)
num_nodes(a)
num_flips(a)
infer(a)
dump_dot(a, "rough3.dot")

bits = 1
pieces = 8
f = uniform_gaussian_eq(pieces, bits, false, false, 1)
a = compile(f)
num_nodes(a)
num_flips(a)
infer(a)
dump_dot(a, "rough3.dot")


