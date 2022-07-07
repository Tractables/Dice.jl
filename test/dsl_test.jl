using Test
using Dice
using Dice: Flip, ifelse
using DirectedAcyclicGraphs

@testset "Control flow macro" begin
    
    f = @dice_ite begin
        if flip(0.5)
            true
        else
            false
        end
    end

    @test f isa Flip
    @test pr(f) ≈ 0.5

    @dice_ite g(p) = begin
        if flip(p)
            true
        else
            false
        end
    end

    @test g(0.42) isa Flip
    @test pr(g(0.42)) ≈ 0.42

    @dice_ite h(p) = begin
        if flip(p)
            flip(0.1)
        else
            flip(0.2)
        end
    end

    @test pr(h(0.42)) ≈ 0.42 * 0.1 + (1-0.42) * 0.2
    
    @test_throws LoadError @eval @dice_ite begin
        x = true
        if flip(0.5)
            x = false
        end
        x
    end

end


@testset "Control flow dynamo" begin

    f = @dice begin
        if flip(0.5)
            true
        else
            false
        end
    end

    @test f.returnvalue isa Flip
    @test pr(f) ≈ 0.5

    g(p) = begin
        if flip(p)
            true
        else
            false
        end
    end

    @test (@dice g(0.42)).returnvalue isa Flip
    @test pr(@dice g(0.42)) ≈ 0.42

    h(p) = begin
        if flip(p)
            flip(0.1)
        else
            flip(0.2)
        end
    end

    @test pr(@dice h(0.42)) ≈ 0.42 * 0.1 + (1-0.42) * 0.2
    
    f2() = begin
        x = true
        if flip(0.6)
            x = false
        end
        x
    end

    @test pr(dice(f2)) ≈ 1 - 0.6

    f2b() = f2() & flip(0.8)
    @test pr(dice(f2b) )≈ (1 - 0.6) * 0.8
    @test pr(@dice f2b()) ≈ (1 - 0.6) * 0.8

    f3 = @dice begin
        x = true
        if flip(0.6)
            x = false
        end
        x
    end

    @test pr(f3) ≈ 1 - 0.6

end

@testset "Error dynamo" begin

    f(p) = if flip(p) 
        error("BAD $p")
        true 
    else 
        false 
    end
    
    x = dice() do 
        f(0.1) || f(0.2) 
    end

    @test length(x.errors) == 2

    @test num_nodes(first(x.errors[1])) == 1
    @test x.errors[1][2].msg == "BAD 0.1"

    @test num_nodes(first(x.errors[2])) == 4
    @test x.errors[2][2].msg == "BAD 0.2"

    @test_throws ProbException pr(x) 

    y = dice() do 
        if flip(0.6)
            error("bad branch")
            observe(false)
            true
        else
            false
        end
    end

    @test pr(y) ≈ 0 # should not throw exception because of observe

end

@testset "Observe dynamo" begin

    f(p) = if flip(p) 
        observe(flip(0.3))
        true 
    else 
        false 
    end
    
    x = dice() do 
        f(0.1) || f(0.2) 
    end

    @test length(x.observations) == 2

    @test num_nodes(x.observations[1]) == 4
    @test num_nodes(x.observations[2]) == 7


    @test pr(x.observations[1]) ≈ (0.9+0.1*0.3)
    @test pr(x.observations[2]) ≈ 0.1+0.9*(0.8+0.2*0.3) # note that this program uses the short-circuited || so the second observe is only called when the first function returns false!

    @test pr(x.observations[1] & x.observations[2]) ≈ 0.1*0.3 + 0.9*(0.8+0.2*0.3)
    @test pr(constraint(x)) ≈ 0.1*0.3 + 0.9*(0.8+0.2*0.3)

    @test pr(x.returnvalue & x.observations[1] & x.observations[2]) ≈ 0.1*0.3+0.9*0.2*0.3

    @test pr(x) ≈ (0.1*0.3+0.9*0.2*0.3) / (0.1*0.3 + 0.9*(0.8+0.2*0.3))

end