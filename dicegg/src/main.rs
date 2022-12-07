#![allow(unused_variables)]
#![allow(unused_imports)]
mod dice_cg;
use dice_cg::*;
use egg::{rewrite as rw, *};

fn main() {
    let mut expr: RecExpr<DiceCG> = RecExpr::default();
    let one = expr.add(DiceCG::Num(1));
    let flip1 = expr.add(DiceCG::Flip(one));
    let two = expr.add(DiceCG::Num(2));
    let flip2 = expr.add(DiceCG::Flip(two));
    let not_flip1 = expr.add(DiceCG::Not(flip1));
    let not_flip1_or_flip2 = expr.add(DiceCG::Or([not_flip1, flip2]));
    let top = expr.add(DiceCG::And([flip1, not_flip1_or_flip2]));


    type DiceLitRunner = Runner<DiceCG, ImpliedLiterals>;
    let runner = DiceLitRunner::default().with_explanations_enabled().with_expr(&expr)
.run(&get_rules());

    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_best_cost, best_expr) = extractor.find_best(runner.roots[0]);


    let (imptrue, impfalse) = &runner.egraph[top].data;

    println!("Expression            {}", expr);
    println!("Rewritten             {}", best_expr);
    print!("Implied when true    ");
    for (id, b) in imptrue {
        if *b {
            print!(" (not flip {}) ∧", runner.egraph.id_to_expr(*id))
        } else {
            print!(" (flip {}) ∧", runner.egraph.id_to_expr(*id)) 
        }
    }
    if imptrue.is_empty() {
        print!(" true")
    }
    println!();

    print!("Implied when false   ");
    for (id, b) in impfalse {
        if *b {
            print!(" (not flip {}) ∧", runner.egraph.id_to_expr(*id))
        } else {
            print!(" (flip {}) ∧", runner.egraph.id_to_expr(*id)) 
        }
    }
    if impfalse.is_empty() {
        print!(" true")
    }
    println!();

    // let mut egraph: EGraph<SymbolLang, ()> = Default::default();
    // egraph.add_expr(&expr);
    // egraph.rebuild();

    // let matches = &and_over_or.search(&egraph);
    // assert!(!matches.is_empty());
    // and_over_or.apply(&mut egraph, &matches);

    // egraph.rebuild();

    // let matches = &complement_law.search(&egraph);
    // assert!(!matches.is_empty());
    // and_over_or.apply(&mut egraph, &matches);
}