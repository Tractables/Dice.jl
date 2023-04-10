using Revise
using Dice

# Without PPL
a_true = 0.3; a_false = 0.7;
b_true = 0.7; b_false = 0.3;
a_true_b_true = 0.3*0.7

# With a PPL
a = flip(0.3); b = flip(0.7);
pr(a & b)

# Values in a program
true

true

# Variables in a program
x = true

x = flip(0.3)
pr(x)

# Tuples
t1 = (true, false)

t1 = @dice begin
            (flip(0.3), flip(0.4))            
end
pr(t1)

# Conditionals in a program
y = if true false else true end

y = @dice if flip(0.3) false else true end
pr(y)

y = @dice if flip(0.3) flip(0.4) else flip(0.5) end
pr(y)



# Sequential statements
let1 = 1
let2 = 2

let1 = flip(0.3)
let2 = flip(0.4)
pr((let1, let2))
pr(let1)
pr(let2)

# Functions
code = @dice begin
                f(x) = if x flip(0.3) else flip(0.4) end
                x = flip(0.3)
                y = f(x)
                y
        end
pr(code)

# Conditional probabilities
code = @dice begin
    function f(x)
        y = x || flip(0.5)
        observe(y)
        y 
    end
    x = flip(0.5)
    y = f(x)
    x
end
pr(code)