using Test
using Alea, Distributions

@testset "Gaussian observations" begin
    
    FP = DistFix{6, 2}
    data = FP(0.0)
    
    @test_broken code = @alea begin
        a = flip(0.5)
        gaussian_observe(FP, 4, -4.0, 4.0, 0.0, 1.0, data)
        a
    end

    # @test pr(code)[false] ≈ 0.5

    FP = DistFix{8, 2}
    data = FP(1.0)

    # test for conjugate gaussians
    map([true, false]) do add_arg
        code = @alea begin
            a = bitblast(FP, Normal(0, 1), 16, -8.0, 8.0)
            gaussian_observe(FP, 8, -8.0, 8.0, a, 1.0, data, add=add_arg)
            a
        end
        @test isapprox(expectation(code), 0.5;) rtol=0.02
    end

    FP = DistFix{5, 1}
    data = FP(1.0)

    map([true, false]) do mult_arg

        code = @alea begin
            a = bitblast(FP, Normal(1, 1), 2, 0.5, 2.5)
            gaussian_observe(FP, 2, -2.0, 2.0, 0.0, a, data, mult=mult_arg)
            a
        end
        @test 1.2 < expectation(code) < 1.6

        code = @alea begin
            m = uniform(FP, -2.0, 2.0)
            a = bitblast(FP, Normal(1, 1), 2, 0.5, 2.5)
            gaussian_observe(FP, 2, -2.0, 2.0, m, a, data, mult=mult_arg)
            m
        end
        @test expectation(code) > 0.1

    end

end

@testset "Parametrised Flip" begin
    l = Vector(undef, 10)
    for i=1:10
        a = parametrised_flip(DistFix{5 + i, 3+i}(0.7))
        p = pr(a)
        l[i] = 0.7 - p[1.0]
    end
    @test reverse(l) == sort(l)

end

@testset "print_tree" begin
    io = IOBuffer()

    leaf = ("Leaf", [])
    print_tree(leaf, io=io)
    @test String(take!(io)) == "Leaf\n"

    tree =
        ("Branch", [
            1,
            ("Branch", [
                2,
                ("Branch", [
                    3,
                    ("Leaf", []),
                    ("Leaf", [])
                ]),
                ("Branch", [
                    4,
                    ("Leaf", []),
                    ("Leaf", [])
                ])
            ]),
            ("Leaf", [])
        ])
    print_tree(tree, io=io)
    @test String(take!(io)) == """
        Branch
        ├── 1
        ├── Branch
        │   ├── 2
        │   ├── Branch
        │   │   ├── 3
        │   │   ├── Leaf
        │   │   └── Leaf
        │   └── Branch
        │       ├── 4
        │       ├── Leaf
        │       └── Leaf
        └── Leaf
        """
end
