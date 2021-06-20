using Pkg; Pkg.activate("Dice/test");
using HTTP
using Dice

# bn = "cancer";
# bn = "survey";
# bn = "alarm";
# bn = "pigs";
# bn = "water";
bn = "munin";

r = HTTP.request("GET", "https://raw.githubusercontent.com/SHoltzen/dice/master/benchmarks/bayesian-networks/$bn.bif.dice"); nothing;
bn_code = String(r.body); nothing;

@time dice_expr = Dice.parse(Dice.DiceProgram, bn_code); nothing;

# manual
# using Lerche
# dice_parser =  Lark(Dice.dice_grammar, parser="lalr", lexer="contextual")
# bn_ast = Lerche.parse(dice_parser, bn_code);
# Lerche.transform(Dice.DiceTransformer(), bn_ast);

@time c = Dice.compile(dice_expr); nothing;

custom_strategy = (Dice.default_strategy()..., categorical = :sangbeamekautz,)
custom_strategy = (Dice.default_strategy()..., branch_elim = :none,)
custom_strategy = (Dice.default_strategy()..., branch_elim = :guard_bdd,)
custom_strategy = (Dice.default_strategy()..., branch_elim = :path_bdd,)
custom_strategy = (Dice.default_strategy()..., branch_elim = :nested_guard_bdd,)
@time c = Dice.compile(dice_expr, Dice.CuddMgr(custom_strategy)); nothing;

Dice.num_nodes(c)
Dice.num_flips(c)
Dice.num_vars(c.mgr)

# ground truth size
Dice.run_dice(bn_code; skiptable=true, determinism=true, showsize=true)
   
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

@time s, _ = Dice.support(dice_expr)
