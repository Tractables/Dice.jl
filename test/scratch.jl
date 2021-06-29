using Dice

mgr = Dice.default_manager()
s = Dice.default_strategy()

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

Dice.compile(mgr, b, Dice.parse(DiceProgram, "let x = int(1,1) in x"))

test = Dice.compile(mgr, b, Dice.parse(DiceProgram, 
raw"""
discrete(0.1, 0.2)
"""))

Dice.num_nodes(test)

Dice.dump_dot(test, "test.dot"); println(read("test.dot", String))

Dice.dump_dot(Dice.flip(mgr), "test.dot"); println(read("test.dot", String))
Dice.dump_dot(!Dice.flip(mgr), "test.dot"); println(read("test.dot", String))

Dice.run_dice("flip 0.5")

Dice.parse(DiceProgram, "true")
Dice.parse(DiceProgram, "false")

Dice.run_dice("discrete(0.1, 0.1, 0.1, 0.1, 0.6)"; skiptable=true, determinism=false, showinternal=true)

# debug
code = raw"""
let i = discrete(0.1, 0.2, 0.3, 0.4) in
    if i == int(2,2) then
        true
    else
        if i == int(2,3) then
            true
        else
            false
"""
# ground truth desugar
Dice.run_dice(code; skiptable=true, determinism=true, showinternal=true)
# ground truth size
Dice.run_dice(code; skiptable=true, determinism=true, showsize=true)
# show bdd
Dice.run_dice(code; skiptable=true, determinism=true, printstatebdd=true)


# Dice.jl size
mgr = Dice.default_manager()
c = Dice.compile(mgr, b, Dice.parse(DiceProgram, code))
Dice.num_nodes(c)
Dice.num_nodes(c; as_add=false)

Dice.dump_dot(c, "test.dot"; as_add=true); println(read("test.dot", String))


Dice.dump_dot(Dice.compile(mgr, b, Dice.parse(DiceProgram, "discrete(0.1, 0.2, 0.7)")), "test.dot"; as_add=true); println(read("test.dot", String))


Dice.dump_dot(Dice.compile(mgr, b, Dice.parse(DiceProgram, raw"""
if flip 0.5 then
    int(0,0)
else if flip 0.5 then
    int(0,1)
else
    int(0,2)
""")), "test.dot"; as_add=true); println(read("test.dot", String))


# code = "discrete(0.1, 0.2, 0.3, 0.2, 0.2)"
code = "discrete(0.000000,0.000000,1.000000)"
Dice.dump_dot(Dice.compile(mgr, b, s, Dice.parse(DiceProgram, code)), "test.dot"; as_add=true); println(read("test.dot", String))
Dice.run_dice(code; skiptable=true, determinism=true, printstatebdd=true)

code = raw"""
if flip 0.09 then
    if flip 0.19 then
        true
    else
        false
else 
    false
"""
custom_strategy = (Dice.default_strategy()..., branch_elim = :nested_guard_bdd,)
c = Dice.compile(code); nothing;
Dice.num_nodes(c)
Dice.dump_dot(c, "test-ok.dot"; as_add=true); 

c = Dice.compile(code, Dice.CuddMgr(custom_strategy)); nothing;
Dice.num_nodes(c)
Dice.dump_dot(c, "test-bad.dot"; as_add=true); 

code = raw"""
let VAR = discrete(0.1,0.9)
in let W = if VAR == int(0,0) then
    discrete(1.0,0.0)
else
    discrete(0.1,0.9)
in (VAR,W)
"""
s, _ = Dice.support(code)
Dice.dump_dot(s, "test.dot"; as_add=true); println(read("test.dot", String))

prefix = "support"
open(prefix * ".log", "w") do out
    open(prefix * ".err", "w") do err
        redirect_stdout(out) do
            redirect_stderr(err) do
                @time s, _ = Dice.support(dice_expr)
                Base.Libc.flush_cstdio()
            end
        end
    end
end


using LightGraphs

g = SimpleGraph()
add_vertex!(g, "ALARM")
add_edge!(g. 1, 2)

using SparseArrays, Metis
S = LightGraphs.smallgraph(:tutte)
parts = Metis.separator(S)

el = Edge.([(i,i+1) for i = 1:12 ])
S = SimpleGraph(el)
collect(edges(S))
perm, _ = Metis.permutation(S); perm
parts = Metis.separator(S)
