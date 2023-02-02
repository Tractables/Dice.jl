using Dice

c = @dice begin 
curValue = uniform(DistInt{10}, 1, 51)
tgtValue = uniform(DistInt{10}, 1, 51)



delta = tgtValue - curValue

for i=1:5
    d = ifelse((delta < DistInt{10}(5)) & (delta > DistInt{10}(-5)), 
        DistInt{10}(0), 
        ifelse(delta < DistInt{10}(0),
            
            ifelse(delta > DistInt{10}(-10),
            delta + uniform(DistInt{10}, -5, 6), 
            ifelse(delta > DistInt{10}(-20), 
            delta + uniform(DistInt{10}, -10, 11), 
            delta + uniform(DistInt{10}, -20, 21))), 
            
            ifelse(delta < DistInt{10}(10), 
            delta + uniform(DistInt{10}, -5, 6), 
            ifelse(delta < DistInt{10}(20), 
            delta + uniform(DistInt{10}, -10, 11), 
            delta + uniform(DistInt{10}, -20, 21)))
        )
    )

    curValue = curValue + d 

    curValue = ifelse(curValue > DistInt{10}(50), 
                    DistInt{10}(50), 
                ifelse(curValue < DistInt{10}(1), 
                    DistInt{10}(1), 
                    curValue))
    
    delta = tgtValue - curValue
end 

(delta < DistInt{10}(5)) && (delta > DistInt{10}(-5))
end


pr(c)