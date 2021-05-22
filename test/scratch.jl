using Dice

mgr = Dice.default_manager()
b = Dice.default_bindings()

t = Dice.compile(mgr, b, true)
f = Dice.compile(mgr, b, false)

Dice.issat(t)
Dice.issat(f)

t1 = Dice.compile(mgr, b, (true,false))
t2 = Dice.compile(mgr, b, (true,false))
t3 = Dice.compile(mgr, b, (true,true))
t4 = Dice.compile(mgr, b, (true,(false,true)))

Dice.prob_equals(t,t)
Dice.prob_equals(t,f)

Dice.prob_equals(t1,t1)
Dice.prob_equals(t1,t2)
Dice.prob_equals(t1,t3)
Dice.prob_equals(t1,t4)

i1 = Dice.compile(mgr, b, 42)
i2 = Dice.compile(mgr, b, 42)
i3 = Dice.compile(mgr, b, 19)
i4 = Dice.compile(mgr, b, 0)

Dice.prob_equals(i1,i1)
Dice.prob_equals(i1,i2)
Dice.prob_equals(i1,i3)

Dice.prob_equals(Dice.compile(mgr, b, 0),Dice.compile(mgr, b, 1))

Dice.ite(f,f,t)

t === Dice.prob_equals(i1,Dice.ite(t,i1,i3))

Dice.max_bits(Dice.ite(t,i1,i4))
Dice.max_bits(Dice.ite(f,i1,i4))

f1 = Dice.flip(mgr)
f2 = Dice.flip(mgr)

Dice.max_bits(Dice.ite(f1,i1,i4))

c1 = Dice.compile(mgr, b, Dice.Categorical([0.0,0.1,0.0,0.9]))
c2 = Dice.compile(mgr, b, Dice.Categorical([0.1,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))
c3 = Dice.compile(mgr, b, Dice.Categorical([0.1,0.1,0.1,0.1,0.1,0.1,0.1,0.1,0.1,0.1]))

using CUDD
Cudd_SharingSize([f1.bit,f2.bit, (f1|f2).bit, (f1|!f2 & Dice.flip(mgr) & Dice.flip(mgr)).bit], 4)

Dice.num_nodes(f1)
Dice.num_nodes(c1)
Dice.num_nodes(c2)
Dice.num_nodes(c3)
Dice.num_nodes(Dice.ite(f1,c3,c1))

Dice.compile(mgr, b, Dice.parse(DiceProgram, "int(1,4)"))
Dice.compile(mgr, b, Dice.parse(DiceProgram, "int(10,4) == int(20,4)"))
Dice.compile(mgr, b, Dice.parse(DiceProgram, "int(10,4) == int(20,5)"))

Dice.compile(mgr, b, Dice.parse(DiceProgram, "if int(10,4) == int(20,5) then discrete(0.1,0.9) else discrete(0.1,0.9)"))