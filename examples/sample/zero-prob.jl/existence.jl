using Dice

# Original Program
w = DistFix{4, 0}([false, false, flip(0.5), flip(0.5)])
x = DistFix{4, 0}([false, false, true, true]) # 3
y = DistFix{4, 0}([false, true, false, true]) # 5
e = DistFix{4, 0}([false, false, flip(0.5), flip(0.5)])
event = prob_equals(w*x+e, y)

pr(event)

# Sampled the last bit
w = DistFix{4, 0}([false, false, flip(0.5), true])
x = DistFix{4, 0}([false, false, true, true]) # 3
y = DistFix{4, 0}([false, true, false, true]) # 5
e = DistFix{4, 0}([false, false, flip(0.5), true])
event = prob_equals(w*x+e, y)

pr(event) # probability is zero

function mult_custom(x::DistFix{W, F}, y::DistFix{W, F}) where {W, F}
    xbig = convert(DistFix{W+F,F}, x)
    ybig = convert(DistFix{W+F,F}, y)
    z_mantissa = xbig.mantissa * ybig.mantissa
    zbig = DistFix{W+F,2F}(z_mantissa)
    zbig
    # convert(DistFix{W,F}, zbig)
end

# Extra bits for ergonomy reasons - to help signed bits and to help upward flow of bits
# Setting y to be 0, so e = wx
w = DistFix{4, 1}([false, false, flip(0.5), flip(0.5)])
x = DistFix{4, 1}([false, false, true, true])
y = DistFix{4, 1}([false, false, false, false])
prod = mult_custom(w, x)
pr(prod)

# Sampled Program
w = DistFix{4, 1}([false, false, flip(0.5), false])
x = DistFix{4, 1}([false, false, true, true])
y = DistFix{4, 1}([false, false, false, false])
prod = mult_custom(w, x)
pr(prod.mantissa.number.bits) # I need a two bit e

# Sampled Program with more number of bits
w = DistFix{10, 7}([false, false, flip(0.5), [false for i in 1:7]...])
x = DistFix{10, 7}([false, false, true, true, [true for i in 1:6]...])
y = DistFix{10, 7}([false, false, false, [false for i in 1:7]...])
prod = mult_custom(w, x)
a = pr(prod.mantissa.number.bits) # I need an eight bit e
keys(a)

pr(prob_equals(prod, DistFix{17, 14}([false,false,false,true,false,true,false,true,false,true, [false for i in 1:7]...])))
