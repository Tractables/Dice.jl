using Dice

c = @dice begin 
curValue = uniform(DistIntOH{-100, 701}, 1, 501)
tgtValue = uniform(DistIntOH{-100, 701}, 1, 501)



delta = tgtValue - curValue

for i=1:1
    d = ifelse((delta < DistIntOH{-100, 701}(5)) & (delta > DistIntOH{-100, 701}(-5)), 
        DistIntOH{-100, 701}(0), 
        ifelse(delta < DistIntOH{-100, 701}(0),
            
            ifelse(delta > DistIntOH{-100, 701}(-25),
            delta + uniform(DistIntOH{-100, 701}, -10, 11), 
            ifelse(delta > DistIntOH{-100, 701}(-50), 
            delta + uniform(DistIntOH{-100, 701}, -20, 21), 
            ifelse(delta > DistIntOH{-100, 701}(-100), 
            delta + uniform(DistIntOH{-100, 701}, -50, 51), 
            delta + uniform(DistIntOH{-100, 701}, -100, 101)))), 
            
            ifelse(delta < DistIntOH{-100, 701}(25),
            delta + uniform(DistIntOH{-100, 701}, -10, 11), 
            ifelse(delta < DistIntOH{-100, 701}(50), 
            delta + uniform(DistIntOH{-100, 701}, -20, 21), 
            ifelse(delta < DistIntOH{-100, 701}(100), 
            delta + uniform(DistIntOH{-100, 701}, -50, 51), 
            delta + uniform(DistIntOH{-100, 701}, -100, 101))))
        )
    )

    curValue = curValue + d 

    curValue = ifelse(curValue > DistIntOH{-100, 701}(500), 
                    DistIntOH{-100, 701}(500), 
                ifelse(curValue < DistIntOH{-100, 701}(1), 
                    DistIntOH{-100, 701}(1), 
                    curValue))
    
    delta = tgtValue - curValue
end 

(delta < DistIntOH{-100, 701}(5)) && (delta > DistIntOH{-100, 701}(-5))
end


pr(c)