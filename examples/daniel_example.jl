using Dice

z = flip(0.5)

x = ifelse(z, flip(0.75), flip(0.5))

y = ifelse(x | z, flip(0.5), flip(0.75))

t = (x, y)

p1 = pr(t)

tx = @dice begin
        observe(x)
        y
end

p2 = pr(tx)

tnotx = @dice begin
    observe(!x)
    y
end

p3 = pr(tnotx)

sum = 0
for i in p1
    print(i[1][1])
    if i[1][1]
        sum = sum + i[2]* log(p2[i[1][2]])
    else
        sum = sum + i[2]*log(p3[i[1][2]])
    end 
end

#### Causal query #####



tzx = @dice begin
    observe(x)
    observe(z)
    y
end

pzx = expectation(tzx)

tnotzx = @dice begin
    observe(x)
    observe(!z)
    y
end

pnotzx = pr(tnotzx)

tznotx = @dice begin
    observe(!x)
    observe(z)
    y
end

pznotx = pr(tznotx)

tnotznotx = @dice begin
    observe(!x)
    observe(!z)
    y
end

pnotznotx = pr(tnotznotx)

pz = pr(z)



sum = 0
for i in p1
    print(i[1][1])
    if i[1][1] & i[1][2]
        sum = sum + i[2]* log(pz[true]*pzx[true] + pz[false]*pnotzx[true])
    elseif i[1][1] & !i[1][2]
        sum = sum + i[2]* log(pz[true]*pzx[false] + pz[false]*pnotzx[false])
    elseif !i[1][1] & i[1][2]
        sum = sum + i[2]* log(pz[true]*pznotx[true] + pz[false]*pnotznotx[true])
    else
        sum = sum + i[2]* log(pz[true]*pznotx[false] + pz[false]*pnotznotx[false])
    end 
end


# tznotx = @dice begin
# observe(!x)
# y
# end

# p3 = pr(tnotx)

