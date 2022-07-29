using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir, uniform

function num_digits(i)
    if i == 0 0 else
    floor(Int, log2(i))+1
    end
end

function Dice.uniform(mgr, b::Int, t::Type)
    if b == 0
        x = Vector(undef, 1)
    else
        x = Vector(undef, b)
    end
    if b == 0
        x[1] = DistBool(mgr, 0.0)
    else
        for i = b:-1:1
            x[i] = DistBool(mgr, 0.5)
        end
    end
    return t(x)
end

function uniform2(mgr, start, stop, t::Type{DistSigned{T, F}}) where T where F

    # no checks for arguments
    start_proxy = start * 2^F
    stop_proxy = Int(stop * 2^F)
    @show (start_proxy, stop_proxy)
    if start_proxy > 0 
        #println(start)
        @show start, stop
        (t(mgr, Float64(start)) + uniform2(mgr, 0.0, stop-start, t))[1]
    else
        is_power_of_two = (stop_proxy) & (stop_proxy-1) == 0
        
        if is_power_of_two 
            #println("is_power_of_two")
            uniform(mgr, num_digits(stop_proxy-1), t) 
        else
            @show stop
            #println("is not")
            power_lt = 2^(num_digits(stop_proxy)-1)
            @show power_lt
            Dice.ifelse(DistBool(mgr, power_lt/stop_proxy),  
                uniform(mgr, num_digits(stop_proxy) - 1, t), 
                uniform2(mgr, power_lt/2^F, stop, t))
        end
    end
end

code = @dice begin
            a = uniform2(dicecontext(), 0.0, 6.0, DistSigned{7, 2})
            a
end

code2 = @dice begin
            binbits = 2
            t = DistSigned{binbits + 5, binbits}
            b = uniform2(dicecontext(), 0.0, 8.0, t)
            a = if (flip(1/2))
                    b
            else
                    (b + t(dicecontext(), 1/2^binbits))[1]
            end
            # a = if flip(1/2^(binbits+3 + 1)) 
            #         t(dicecontext(), 0.0)
            #     else
            #         # t(dicecontext(), 10.0)
            #         if flip(1/(2^(binbits+3+1)-1))
            #             t(dicecontext(), 8.0)
            #         else
            #             uniform2(dicecontext(), 1/2^binbits, 8.0, t)
            #             # t(dicecontext(), 0.5)
            #         end
            #     end
            a

end

b = compile(code2)
num_flips(b)
num_nodes(b)
a = infer(code2, :bdd)