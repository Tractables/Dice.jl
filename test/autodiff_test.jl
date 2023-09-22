using Dice
using Test

@testset "test autodiff" begin
    x = new_var!("x", 5)
    e = x^2
    derivs = differentiate(Dict(e => π))
    @test derivs[x] ≈ 10 * π
    clear_vars!()

    x = new_var!("x", 5)
    e = 1/x
    derivs = differentiate(Dict(e => π))
    @test derivs[x] ≈ -1/25 * π
    clear_vars!()
end

@testset "test GD" begin
    x = new_var!("x", 0)
    e = 7 - (x-5)^2
    for _ in 1:100
        step_maximize!([e], 0.1)
    end
    @test compute(e) ≈ 7
    @test compute(x) ≈ 5
    clear_vars!()

    x = new_var!("x", 7)
    y = new_var!("y", 1)
    e = -(x*y-5)^2
    for i in 1:100
        step_maximize!([e], 0.01)
    end
    vals = Dict{ADNode, Real}()
    @test abs(compute(e, vals)) < 0.001
    @test compute(x, vals) * compute(y, vals) ≈ 5
    clear_vars!()

    
    psp = new_var!("psp", 0) # pre-sigmoid probability
    p = sigmoid(psp)
    # maximize logpr of flip(p) & flip(p) & !flip(p)
    e = log(p * p * (1 - p))
    for i in 1:500
        step_maximize!([e], 0.1)
    end
    @test compute(p) ≈ 2/3
    clear_vars!()
end

@testset "matrices" begin
    # Helper functions for matrices used as vectors
    x(v) = v[1,1]
    y(v) = v[2,1]
    distance(u, v) = (x(u) - x(v))^2 + (y(u) - y(v))^2
    to_matrix(v::Vector) = reshape(v, :, 1)

    # Rotate [1, 2] by what angle to get closest to [-3, -3]?
    θ = new_var!("θ", 0)
    rotation_matrix = ADMatrix([[cos(θ) -sin(θ)]; [sin(θ) cos(θ)]])
    rotated_vec = rotation_matrix * to_matrix([1, 2])
    target_vec = to_matrix([-3, -3])
    train_vars!(-distance(rotated_vec, target_vec))

    @test value(θ) ≈ 5/8 * 2π - atan(2)
    clear_vars!()

    # Variables can also be matrices!
    # Transform by [1, 2] by what matrix to get closest to [-3, -3]?
    A = new_var!("A", [[1 0]; [0 1]])
    v = to_matrix([1, 2])
    v′ = A * v
    target_vec = to_matrix([-3, -3])
    compute(A * v)
    train_vars!(-distance(v′, target_vec))

    @test compute(A) * v ≈ [-3, -3]
    clear_vars!()
end

clear_vars!()

