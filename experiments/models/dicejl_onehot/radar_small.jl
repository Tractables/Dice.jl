using Dice
using BenchmarkTools

function fun() 

    c = @dice begin
        w = 10
        
        function T(mu, l, r) 
            x = uniform(DistInt{w}, -l, 1) + uniform(DistInt{w}, 0, l+1)
            y = uniform(DistInt{w}, -r, 1) + uniform(DistInt{w}, 0, r+1)
            observe(x <= DistInt{w}(0) && y > DistInt{w}(0))

            return ifelse(flip(l/(l+r)), x, y) + mu
        end
        
        b1 = flip(0.2)
        b2 = ifelse(b1, true, flip(0.2))
        x1 = uniform(DistInt{w}, 0, 11)
        x2 = uniform(DistInt{w}, -2, 3) + x1 

        o1 = x1 + ifelse(b1, T(x1, 5, 1), T(x1, 5, 5))
        o2 = x2 + ifelse(b2, T(x2, 5, 1), T(x2, 5, 5))

        observe(o1 == DistInt{w}(5));
        observe(b1)

        x2 

        # T(DistInt{w}(0), 5, 5)
    end
    pr(c)
end 
x = @benchmark fun()

println(dump(x))
