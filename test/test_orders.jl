using Pkg; Pkg.activate("Dice/test");
using Dice

function gen_code(nbcols = 10, nbrows = 7)
    code = ""
    for row = 1:nbrows
        for col = 1:nbcols
            if row == 1
                p = rand()
                code *= """
                        let x$(row)y$(col) = discrete($p, $(1-p)) in
                        """
            else
                p1 = rand()
                p2 = rand()
                code *= """
                        let x$(row)y$(col) = if x$(row-1)y$(col) == int(1,0) then 
                                discrete($p1, $(1-p1)) 
                            else 
                                discrete($p2, $(1-p2)) in
                        """
            end
        end
    end
    for col = 1:nbcols
        if col == 1
            p1 = rand()
            p2 = rand()
            code *= """
                    let z$col = if x$(nbrows)y$(col) == int(1,0) then 
                            discrete($p1, $(1-p1)) 
                        else 
                            discrete($p2, $(1-p2)) in
                    """
        else
            p1 = rand()
            p2 = rand()
            p3 = rand()
            p4 = rand()
            code *= """
                    let z$col = if x$(nbrows)y$(col) == int(1,0) then 
                            if z$(col-1) == int(1,0) then 
                                discrete($p1, $(1-p1)) 
                            else 
                                discrete($p2, $(1-p2))
                        else 
                            if z$(col-1) == int(1,0) then 
                                discrete($p3, $(1-p3)) 
                            else 
                                discrete($p4, $(1-p4)) in
                    """
        end
    end

    rtuple = ""
    for row = 1:nbrows
        for col = 1:nbcols
            if row ==1 && col ==1
                rtuple = "x1y1"
            else
                rtuple = "(x$(row)y$(col),$rtuple)"
            end
        end
    end
    for col = 1:nbcols
        rtuple = "(z$(col),$rtuple)"
    end

    code *= rtuple
    code
end

@time code = gen_code(); nothing
# println(code)
@time dice_expr = Dice.parse(Dice.DiceProgram, code); nothing;
@time c = Dice.compile(dice_expr); nothing;
Dice.num_nodes(c)

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

custom_strategy = (Dice.default_strategy()..., debug=1, var_order = :program_order,)
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