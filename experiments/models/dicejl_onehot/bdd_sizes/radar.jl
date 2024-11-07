using Dice
using BenchmarkTools

function fun() 

    c = @dice begin
        # w = 10
        
        function T(mu, l, r) 
            x = uniform(DistIntOH{-8, 30}, -l, 1) + uniform(DistIntOH{-8, 30}, 0, l+1)
            y = uniform(DistIntOH{-8, 30}, -r, 1) + uniform(DistIntOH{-8, 30}, 0, r+1)
            observe(x <= DistIntOH{-8, 30}(0) && y > DistIntOH{-8, 30}(0))

            return ifelse(flip(l/(l+r)), x, y) + mu
        end
        
        b1 = flip(0.2)
        b2 = ifelse(b1, true, flip(0.2))
        x1 = uniform(DistIntOH{-8, 30}, 0, 11)
        x2 = uniform(DistIntOH{-8, 30}, -2, 3) + x1 

        o1 = x1 + ifelse(b1, T(x1, 5, 1), T(x1, 5, 5))
        o2 = x2 + ifelse(b2, T(x2, 5, 1), T(x2, 5, 5))

        observe(o1 == DistIntOH{-8, 30}(5));
        observe(b1)

        x2 

        # T(DistIntOH{-8, 30}(0), 5, 5)
    end
    debug_info_ref = Ref{CuddDebugInfo}()
    pr(c, algo=Cudd(debug_info_ref=debug_info_ref))
    println("NUM_NODES_START")
    println(debug_info_ref[].num_nodes)
    println("NUM_NODES_END")
end 

fun()