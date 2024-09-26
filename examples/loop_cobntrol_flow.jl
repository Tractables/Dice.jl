using Dice

a = @dice begin 
        x = 0
        for i in 1:1000
            x = if flip(0.5)
                flip(0.7)
            else flip(0.3)
            end
        end
        x
    end

pr(a)