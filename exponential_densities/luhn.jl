using Revise
using Dice
using Plots

n = 6
# original: 3 0 6 5 
id_obs = [9, 0, 5, 1, 6, 6]
# swaps: 5/6, 1/7, 4/9, 9 => 0 
observed_nums = Vector(undef, n) 
for i in 1:n 
    num = id_obs[i]
    if num == 1
        observed_nums[i] = ifelse(flip(0.3), DistUInt{7}(1), ifelse(flip(5/6), DistUInt{7}(7), uniform(DistUInt{7}, 0, 10)))
    elseif num == 4 
        observed_nums[i] = ifelse(flip(0.3), DistUInt{7}(4), ifelse(flip(5/6), DistUInt{7}(9), uniform(DistUInt{7}, 0, 10)))
    elseif num == 5
        observed_nums[i] = ifelse(flip(0.3), DistUInt{7}(5), ifelse(flip(5/6), DistUInt{7}(6), uniform(DistUInt{7}, 0, 10)))
    elseif num == 6
        observed_nums[i] = ifelse(flip(0.3), DistUInt{7}(6), ifelse(flip(5/6), DistUInt{7}(5), uniform(DistUInt{7}, 0, 10)))
    elseif num == 7
        observed_nums[i] = ifelse(flip(0.3), DistUInt{7}(7), ifelse(flip(5/6), DistUInt{7}(1), uniform(DistUInt{7}, 0, 10)))
    elseif num == 9
        observed_nums[i] = ifelse(flip(0.3), DistUInt{7}(9), ifelse(flip(5/6), DistUInt{7}(4), uniform(DistUInt{7}, 0, 10)))
    else 
        observed_nums[i] = ifelse(flip(0.3), DistUInt{7}(num), uniform(DistUInt{7}, 0, 10))
    end 
end

c = @dice begin
    id = [uniform(DistUInt{7}, 0, 10) for in in 1:n]

    sum = DistUInt{7}(0)
    for i in 2:n
        if i % 2 == n % 2
            sum = sum +  ifelse(id[i] > DistUInt{7}(4), DistUInt{7}(2) * id[i] - DistUInt{7}(9), DistUInt{7}(2) * id[i])
        else 
            sum = sum + id[i]
        end 
    end 
    
    a = (sum % DistUInt{7}(10)) 
    b = (DistUInt{7}(10) - a)
    check_digit =  b % DistUInt{7}(10)

    observe(prob_equals(id[1], check_digit))

    # for i in 1:n
    #     observe(prob_equals(id[i], observed_nums[i]))
    # end


    transpose = Vector(undef, n-1)
    transpose[1] = flip(0.1)
    for i in 2:n-1 
        transpose[i] = !transpose[i-1] & flip(0.1)
    end 

  
    
    observe(prob_equals(id[1], ifelse(transpose[1], observed_nums[2], observed_nums[1])))

    for i in 2:n-1
        observe(prob_equals(id[i], ifelse(transpose[i-1], observed_nums[i-1], ifelse(transpose[i], observed_nums[i+1], observed_nums[i]))))
    end 
    observe(prob_equals(id[n], ifelse(transpose[n-1], observed_nums[n-1], observed_nums[n])))
    
    # (id[1], id[2], id[3], id[4])
    # (id[1], sum)
    # (sum, a, b, check_digit)
    (id[1], sum, a, b, check_digit)
end 

pr(allobservations(c))
@time x = pr(c, ignore_errors=true)
sort(collect(x), by=x->x[2], rev=true)