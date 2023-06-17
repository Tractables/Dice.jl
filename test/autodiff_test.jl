using Dice
using Test

@testset "test autodiff" begin
    x = add_param!("x", 5)
    e = x^2
    values = compute([e])
    derivs = differentiate(Dict(e => π))
    @test derivs[x] ≈ 10 * π
    clear_params!()

    x = add_param!("x", 5)
    e = 1/x
    values = compute([e])
    derivs = differentiate(Dict(e => π))
    @test derivs[x] ≈ -1/25 * π
    clear_params!()
end

@testset "test GD" begin
    x = add_param!("x", 0)
    e = 7 - (x-5)^2
    for _ in 1:100
        step_maximize!([e], 0.1)
    end
    values = compute([e])
    @test values[e] ≈ 7
    @test values[x] ≈ 5
    clear_params!()

    x = add_param!("x", 7)
    y = add_param!("y", 1)
    e = -(x*y-5)^2
    for i in 1:100
        step_maximize!([e], 0.01)
    end
    values = compute([e])
    @test abs(values[e]) < 0.001
    @test values[x] * values[y] ≈ 5
    clear_params!()

    
    sigmoid(x) = 1 / (1 + exp(-x))
    psp = add_param!("psp", 0) # pre-sigmoid probability
    p = sigmoid(psp)
    # maximize logpr of flip(p) & flip(p) & !flip(p)
    e = log(p * p * (1 - p))
    for i in 1:500
        step_maximize!([e], 0.1)
    end
    values = compute([e])
    @test values[p] ≈ 2/3
    clear_params!()
end