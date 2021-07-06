using Pkg; Pkg.activate("Dice/test");
using Dice

function gen_code(n = 7)
    code = ""
    for row = 1:n
            if row == 1
                p = rand()
                code *= """
                        let x$(row) = discrete($p, $(1-p)) in
                        """
            else
                p1 = rand()
                p2 = rand()
                code *= """
                        let x$(row) = if x$(row-1) == int(1,0) then 
                                discrete($p1, $(1-p1)) 
                            else 
                                discrete($p2, $(1-p2)) in
                        """
            end
    end

    rtuple = ""
    for row = 1:n
            if row ==1
                rtuple = "x1"
            else
                rtuple = "(x$(row),$rtuple)"
            end
    end

    code *= rtuple
    code
end


macro timeout(seconds, expr)
    quote
        tsk = @task $expr
        schedule(tsk)
        Timer($seconds) do timer
            istaskdone(tsk) || Base.throwto(tsk, InterruptException())
        end
        fetch(tsk)
    end
end

part_order(x) =
    if isempty(x)
        []
    else
        mid = ceil(Int,length(x)/2)
        bef = part_order(x[1:mid-1])
        aft = part_order(x[mid+1:end])
        inter = [bef aft[1:length(bef)]]'[:]
        r = [x[mid], inter..., aft[length(bef)+1:end]...]
        @assert length(r) == length(x) "$r from $x"
        r
    end

for i in 5:5:45
    println("Chain of length $i")
    code = gen_code(i); nothing
    dice_expr = Dice.parse(Dice.DiceProgram, code); nothing;

    for or in [:topological, :reverse_topological, :graph_partitioning, :graph_partitioning_reverse]
        π::Vector{Int} = if or == :topological
            1:i
        elseif or == :reverse_topological
            i:-1:1
        elseif or == :graph_partitioning
            part_order(1:i)
        elseif or == :graph_partitioning_reverse
            reverse(part_order(1:i))
        else
            error(or)
        end
        
        custom_strategy = (Dice.default_strategy()..., debug=0, 
            var_order = π,)
        # categorical = :sangbeamekautz
        # c = Dice.compile(dice_expr); nothing;
        (c = Dice.compile(dice_expr, Dice.CuddMgr(custom_strategy)); nothing;)
        s = Dice.num_nodes(c)
        println("  - $or compiles to $s nodes")
    end    
end


custom_strategy = (Dice.default_strategy()..., debug=1, var_order = :dfs,)
custom_strategy = (Dice.default_strategy()..., debug=1, var_order = :metis_cut,)
custom_strategy = (Dice.default_strategy()..., debug=1, var_order = :metis_perm,)
custom_strategy = (Dice.default_strategy()..., debug=1, var_order = :metis_perm_rev,)
custom_strategy = (Dice.default_strategy()..., debug=1, var_order = :min_gap,)
(c = @timeout 60 (Dice.compile(dice_expr, Dice.CuddMgr(custom_strategy)))); nothing
Dice.num_nodes(c)

g = Dice.id_dep_graph(dice_expr); nothing;
Dice.plot(g);
Dice.plot(g; order = :program_order);
Dice.plot(g; order = :dfs);
Dice.plot(g; order = :metis_cut);

Dice.plot_cut(g);

open("test.dice", "w") do io
    write(io, code)
end;