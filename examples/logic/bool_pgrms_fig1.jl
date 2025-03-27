using Alea

# hack to allow us to use non-functional probabilistic ITE
Base.ifelse(::Dist{Bool}, ::Any, ::Nothing) = DistUInt32(77)
Base.ifelse(::Dist{Bool}, ::Nothing, ::Any) = DistUInt32(77)

choice() = flip(0.5)

function main()
c1, c2 = choice(), choice()
y = c1
function getUnit()
    x = false 
    if y
        if c2
            y = false  # deleting this causes a ProbException (as it should)
            x = true
        end
    else
        x = true
    end

    if x
        if y
            error("assert(F)")
        end
    end
end

    getUnit()
    false  # dummy return value
end

md = @dice main()
pr(md)


# ~~ Software model checking-style safety analysis ~~
# A single-rooted BDD represents possible program states (maps var assignment to
# validity) - vars are program vars.
function getUnit()
    x = false
    # !x
    if y
        # !x & y
        if choice()
            y = false
            x = true
            # x & !y
        end
        # !x & y | x & !y
    else
        # !x & !y 
        x = true
        # x & !y
    end
    # (!x & y | x & !y) | (x & !y)
    # aka
    # !x & y | x & !y

    if x
        # x & !y
        if y
            # false
            error("assert(F)")
        end
    end
end



# ~~ Alea-style safety analysis ~~
# Multi-rooted BDD representing program states; vars are choices.
function getUnit()
    x = false
    # x = false; y = c1; path=[]
    if y
        # x = false; y = c1; path=[c1]
        if choice()
            # x = false; y = c1; path=[c1, c2]
            y = false
            x = true
            # x = true; y = false; path=[c1, c2]
        end
        # x = c2; y = c1 & !c2; path=[c1]
    else
        # x = false; y = c1; path=[!c1]
        x = true
        # x = true; y = c1; path=[!c1]
    end
    # x = (c1 & c2) | !c1; y = c1 & !c2; path=[]

    if x
        # x = ""; y = ""; path=[(c1 & c2) | !c1]
        if y
            # x = ""; y = ""; path=[(c1 & c2) | !c1, c1 & !c2]
            # reduce(&, path) == false
            error("assert(F)")
        end
    end
end
