using Dice, Plots

# classic programs are probabilistic programs 

pr(@dice true)

pr(@dice DistInt(42))

pr(@dice DistInt(42+2))

pr(@dice DistInt(42)+DistInt(2))
bar(ans)


#####################################################
# random variables are first class

pr(@dice flip(0.5))
bar(ans)

pr(@dice discrete(DistUInt8, [.0190, .0010, 0.0560, 0.0240, .1620, .0180, .0072, .7128]))
bar(ans)


# ask for a specific values

probabilities = pr(@dice discrete(DistUInt8, [.0190, .0010, 0.0560, 0.0240, .1620, .0180, .0072, .7128]))
probabilities[7]

x = @dice begin
    world_id = discrete(DistUInt8, [.0190, .0010, 0.0560, 0.0240, .1620, .0180, .0072, .7128])
    prob_equals(world_id, DistUInt8(7))
end
pr(x) 


# control flow

x = @dice begin
    if flip(0.9)
        true
    else
        false
    end
end
pr(x)

x = @dice begin
    if flip(0.9)
        DistInt(42)
    else
        DistInt(1337)
    end
end
pr(x)


# joint probability tables

function mytable() 
    world_id = discrete(DistUInt8, [.0190, .0010, 0.0560, 0.0240, .1620, .0180, .0072, .7128])
    if prob_equals(world_id, DistUInt8(0))
        (true, true, true)
    elseif prob_equals(world_id, DistUInt8(1))
        (true, true, false)
    elseif prob_equals(world_id, DistUInt8(2))
        (true, false, true)
    elseif prob_equals(world_id, DistUInt8(3))
        (true, false, false)
    elseif prob_equals(world_id, DistUInt8(4))
        (false, true, true)
    elseif prob_equals(world_id, DistUInt8(5))
        (false, true, false)
    elseif prob_equals(world_id, DistUInt8(6))
        (false, false, true)
    else
        (false, false, false)
    end
end

pr(@dice mytable())



#####################################################
# what about events that are more than a single world?

function unlucky(world) 
    earthquake, burglery, alarm = world
    earthquake | burglery
end

pr(@dice unlucky(mytable())) !?


# what do we expect to get here?

function secret(world) 
    # DO NOT READ -- MAGIC
    x, y, z = world
    (x | y & z) & (!x | !z) | (!y & z)
end

pr(@dice secret(mytable())) !?


# Axiom 1

pr(@dice secret(mytable()))[true] > 0 !?

pr(@dice secret(mytable()))[true] > 0


# Axiom 2

x = @dice begin
    world = mytable()
    secret(world) | !secret(world)
end

pr(x)[true] !?

pr(x)[true]


# Axiom 3

function myevents()
    world = mytable()
    earthquake, burglery, alarm = world
    x = secret(world) & alarm
    y = secret(world) & !alarm
    z = x | y
    (x,y,z)
end

pr(@dice myevents()[1])[true] + pr(@dice myevents()[2])[true] - pr(@dice myevents()[3])[true]


# what do we expect to get here? now we know

pr(@dice secret(mytable()))


# what do we expect to get here?

code = @dice begin
    earthquake, burglery, alarm = mytable()
    observe(earthquake)
    alarm
end

pr(code)[true] !?


# reduce to what we know

condition = @dice begin
    earthquake, burglery, alarm = mytable()
    earthquake
end

pr(condition)[true]


both = @dice begin
    earthquake, burglery, alarm = mytable()
    alarm & earthquake
end

pr(both)[true]


# find out

pr(both)[true] / pr(condition)[true]

pr(code)[true]


#####################################################
# power of conditioning on evidence

alarm_goes_off = @dice begin
    earthquake, burglery, alarm = mytable()
    alarm
end

pr(alarm_goes_off)[true]

alarm_given_no_earthquake = @dice begin
    earthquake, burglery, alarm = mytable()
    observe(!earthquake)
    alarm
end

pr(alarm_given_no_earthquake)[true]

#####################################################

# betting

a = flip(0.4)
mybet = 60
yourbet = -40

pr(a)[true] * mybet + pr(a)[false] * yourbet


#####################################################

# product rule

both = @dice begin
    earthquake, burglery, alarm = mytable()
    alarm & earthquake
end

pr(both)[true]


# Can I write this without Boolean operators?

alarm_goes_off = @dice begin
    earthquake, burglery, alarm = mytable()
    alarm
end

pr(alarm_goes_off)[true]


earthquake_given_alarm_goes_off = @dice begin
    earthquake, burglery, alarm = mytable()
    observe(alarm)
    earthquake
end

pr(earthquake_given_alarm_goes_off)[true]


pr(alarm_goes_off)[true] * pr(earthquake_given_alarm_goes_off)[true]

pr(both)[true]

#####################################################

# what's the effect of burglery on earthquake?

earthquake_given_burglery = @dice begin
    earthquake, burglery, alarm = mytable()
    observe(burglery)
    earthquake
end

pr(earthquake_given_burglery)[true]

#####################################################

flip(done)

#####################################################

# # Without PPL
# a_true = 0.3; a_false = 0.7;
# b_true = 0.7; b_false = 0.3;
# a_true_b_true = 0.3*0.7

# # With a PPL
# a = flip(0.3); b = flip(0.7);
# pr(a & b)

# # Values in a program
# true

# true

# # Variables in a program
# x = true

# x = flip(0.3)
# pr(x)

# # Tuples
# t1 = (true, false)

# t1 = @dice begin
#             (flip(0.3), flip(0.4))            
# end
# pr(t1)

# # Conditionals in a program
# y = if true false else true end

# y = @dice if flip(0.3) false else true end
# pr(y)

# y = @dice if flip(0.3) flip(0.4) else flip(0.5) end
# pr(y)



# # Sequential statements
# let1 = 1
# let2 = 2

# let1 = flip(0.3)
# let2 = flip(0.4)
# pr((let1, let2))
# pr(let1)
# pr(let2)

# # Functions
# code = @dice begin
#                 f(x) = if x flip(0.3) else flip(0.4) end
#                 x = flip(0.3)
#                 y = f(x)
#                 y
#         end
# pr(code)

# # Conditional probabilities
# code = @dice begin
#     function f(x)
#         y = x || flip(0.5)
#         observe(y)
#         y 
#     end
#     x = flip(0.5)
#     y = f(x)
#     x
# end
# pr(code)

# sing Dice
# ​
# # thoughts: 
# # it would be nice to hide the distint syntax
# # also unsure if the @dice blocks are necessary 
# ​
# ​
# a = 3
# b = if a<5 5 else 3 end
# b
# ​
# ​
# # introducing randomness 
# c = @dice begin 
#     flip(0.7)
# end 
# c
# pr(c)
# ​
# ​
# ​
# c = @dice begin 
#     f1 = flip(0.7)
#     r = if f1 DistInt8(5) else DistInt8(3) end 
#     r 
# end 
# pr(c)
# ​
# ​
# # operations 
# c = @dice begin 
#     f1 = flip(0.7)
#     f2 = flip(0.3)
#     a = if f1 DistInt8(5) else DistInt8(3) end 
#     b = if f2 DistInt8(4) else DistInt8(0) end 
#     a + b
# end 
# pr(c)
# ​
# ​
# # conditioning 
# c = @dice begin 
#     f1 = flip(0.7)
#     f2 = flip(0.3)
#     a = if f1 DistInt8(5) else DistInt8(3) end 
#     b = if f2 DistInt8(4) else DistInt8(0) end 
#     observe(f1)
#     a+b 
# end 
# pr(c)
# ​
# ​
# ​
# ​
# ​
# # independence
# ​
# ​
# ​
# ​
# # conditional independence 