using Revise
using Dice
using Plots

for l=1:5
    code = @dice begin
        a = uniform(DistUInt{2*l}, l)
        b = a*a
        b
    end
    p = pr(code)

    mgr = CuddMgr()
    bdd, cache = compile(mgr, returnvalue(code))
    dump_dot(mgr, bdd, "squaring"*string(l)*".dot")
    println(num_bdd_nodes(mgr, bdd))
end

