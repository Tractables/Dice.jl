using Revise
using Dice

#Ryan's program

x = uniform(DistUInt{3})
y = DistUInt{3}(0)
for i = 0:7
    y = ifelse(prob_equals(x, DistUInt{3}(i)), uniform(DistUInt{3}, 0, i+1), y)
end

pr(y)

pr(y.bits[1])
pr(y.bits[2], evidence = !y.bits[1])
pr(y.bits[3])

x = uniform(DistUInt{3})
y = uniform(DistUInt{3}, 0, 4)
pr((x < y) | prob_equals(x, y))

code = @dice begin

            if prob_equals(x, DistUInt{3}(0))
                    uniform(DistUInt{3}, 0, 8)
            else if prob_equals(x, DistUInt{3}(1))
                    uniform(DistUInt{3}, 1, 8)
            else if prob_equals(x, DistUInt{3}(2))
                    uniform(DistUInt{3}, 2, 8)
            else if prob_equals(x, DistUInt{3}(3))
                    uniform(DistUInt{3}, 3, 8)
            else if prob_equals(x, DistUInt{3}(4))
                    uniform(DistUInt{3}, 4, 8)
            else if prob_equals(x, DistUInt{3}(5))
                    uniform(DistUInt{3}, 5, 8)
            else if prob_equals(x, DistUInt{3}(6))
                    uniform(DistUInt{3}, 6, 8)
            else
                    uniform(DistUInt{3}, 7, 8)
            end end end end end end end
end     
pr(code)

DFiP = DistUInt{2}

pr(uniform(DistUInt{3}, 1, 8))


x = uniform(DFiP)
y = uniform(DFiP)
code = @dice begin
            if flip(3/4) 
                observe(x < y)
            else 
                observe(true)
            end
            y
end

actual = pr(code)
plot(pr(code))

code2 = @dice begin
            observe(x < y)
            x
end
pr(code2)
plot(pr(code2))

pr(x)

a = pr(x; evidence = (x < y))
b = pr(x)
c = Vector(undef, 16)
for i in 1:16
    c[i] = (a[i-1] + b[i-1])*0.5
end

(actual[1] - b[1])/(a[1] - b[1])
(actual[2] - b[2])/(a[2] - b[2])

c
maximum(ans)
pr(x < y)


burglary = flip(0.5)
earthquake = flip(0.5)

alarm = @dice begin
    if (burglary)
        (if (earthquake) 
            flip(0.95)
        else
            flip(0.1)
        end)
    else
        flip(0.01)
    end
end

dist_a1 = discrete(DistUInt{8}, [0.7, 0.3])

a = @dice if flip(0.5) flip(0.3) else flip(0.7) end

a = ifelse(flip(0.5), flip(0.3), flip(0.7))

x3 = flip(0.5)
x2 = flip(0.5)
x1 = flip(0.5)
hi = DistUInt{3}([x3, x2, x1])

u3 = uniform(DistUInt{3}) < hi
pr(u3)


