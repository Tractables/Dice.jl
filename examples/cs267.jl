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

earthquake_without_given_burglery = @dice begin
    earthquake, burglery, alarm = mytable()
    # observe(burglery)
    earthquake
end

pr(earthquake_without_given_burglery)[true]

#####################################################

# we have been using the joint probability table as our distribution
pr(@dice mytable())


# let us focus on the marginal distributin on just earthquake and burglery

earthquak_burglary = @dice begin
    earthquake, burglery, alarm = mytable()
    earthquake, burglery
end

pr(earthquak_burglary)


# there is a better way to write this using what we have learned of independence

earthquak_burglary2 = @dice begin
    earthquake = flip(0.1)
    burglery = flip(0.2)
    earthquake, burglery
end

pr(earthquak_burglary2)


# how do we incorporate alarm?

pr(alarm_goes_off)[true]
pr(alarm_given_no_earthquake)[true]


# product rule to the rescue

function earthquake_burglary_alarm()
    earthquake = flip(0.1)
    burglery = flip(0.2)
    if earthquake & burglery
        alarm = flip(0.95)
    elseif earthquake & !burglery
        alarm = flip(0.7)
    elseif !earthquake & burglery
        alarm = flip(0.9)
    else # !earthquake & !burglery
        alarm = flip(0.01)
    end
    earthquake, burglery, alarm
end

pr(@dice earthquake_burglary_alarm())

#####################################################

# recall that burglary and earthquake were independent
# what's the effect of burglery on earthquake, given alarm?

burglary_given_alarm = @dice begin
    earthquake, burglery, alarm =  earthquake_burglary_alarm()
    observe(alarm)
    burglery
end;

pr(burglary_given_alarm)[true]

burglary_given_alarm_earthquake = @dice begin
    earthquake, burglery, alarm =  earthquake_burglary_alarm()
    observe(alarm & earthquake)
    burglery
end;

pr(burglary_given_alarm_earthquake)[true]

#####################################################

# let's add another variable to our distribution

function alarm_network()
    earthquake, burglery, alarm =  earthquake_burglary_alarm()
    if alarm
        neighborcall = flip(0.9)
    else 
        neighborcall = flip(0.05)
    end
    earthquake, burglery, alarm, neighborcall
end

pr(@dice alarm_network())


# the neighbor calling clearly affects the probability of burglary

burglary_given_call = @dice begin
    earthquake, burglery, alarm, neighborcall = alarm_network()
    observe(neighborcall)
    burglery
end;

pr(burglary_given_call)[true]


# we already know that alarm also affects this probability

pr(burglary_given_alarm)[true]


# what if we know both?

burglary_given_alarm_call = @dice begin
    earthquake, burglery, alarm, neighborcall = alarm_network()
    observe(alarm & neighborcall)
    burglery
end;

pr(burglary_given_alarm_call)[true]

#####################################################

function spamfilter(words) 
    spam = flip(1/2)

    casino = ifelse(spam, flip(0.1), flip(0.005))
    cs267a = ifelse(spam, flip(0.001), flip(0.1))
    homework = ifelse(spam, flip(0.01), flip(0.05))

    observe(prob_equals(casino, "casino" ∈ words))
    observe(prob_equals(cs267a, "cs267a" ∈ words))
    observe(prob_equals(homework, "homework" ∈ words))

    spam
end;


pr(@dice spamfilter(["cs267a", "homework", "is", "due"]))[true]

pr(@dice spamfilter(["join", "my", "casino"]))[true]

pr(@dice spamfilter(["I", "do", "cs267a", "homeworks", "in", "a", "casino"]))[true]

#####################################################

flip(done)

#####################################################
