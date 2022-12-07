use egg::{rewrite as rw, *};
use std::{collections::HashSet, hash::Hash};

define_language! {
    pub enum DiceCG {
        "false" = False,
        "true" = True,
        "!" = Not(Id),
        "&" = And([Id; 2]),
        "|" = Or([Id; 2]),
        "ite" = Ite([Id; 3]),
        "flip" = Flip(Id),  // can we limit the arg to ints?
        Num(i32),
        Symbol(Symbol),
    }
}

#[derive(Default)]
pub struct ImpliedLiterals;
impl Analysis<DiceCG> for ImpliedLiterals {
    type Data = (HashSet<(Id, bool)>, HashSet<(Id, bool)>);

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        let to0len = to.0.len();
        let to1len = to.1.len();
        let from0len = from.0.len();
        let from1len = from.1.len();

        to.0.extend(from.0);
        to.1.extend(from.1);

        return DidMerge(
            to0len != to.0.len() || to1len != to.1.len(),
            from0len != to.0.len() || from1len != to.1.len(),
        );
    }

    fn make(egraph: &EGraph<DiceCG, Self>, enode: &DiceCG) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.clone();
        return match enode {
            DiceCG::Not(a) => (x(a).1, x(a).0),
            DiceCG::And([a, b]) => (
                &x(a).0 | &x(b).0,
                &x(a).1 & &x(b).1,
            ),
            DiceCG::Or([a, b]) => (
                &x(a).0 & &x(b).0,
                &x(a).1 | &x(b).1,
            ),
            DiceCG::Ite([i, t, e]) => (
                &x(t).0 & &x(e).0,
                &x(t).1 & &x(e).1,
            ),
            DiceCG::Flip(id) => (
                HashSet::from([(id.clone(), false)]),
                HashSet::from([(id.clone(), true)])
            ),
            _ => (HashSet::new(), HashSet::new()),
        };
    }
}

// TODO: use rules from https://github.com/egraphs-good/egg/blob/main/tests/prop.rs
pub fn get_rules() -> [Rewrite<DiceCG, ImpliedLiterals>; 4] {
    let rules: [Rewrite<DiceCG, ImpliedLiterals>; 4] = [
        rw!("and-commutative"; "(& ?x ?y)" => "(& ?y ?x)"),
        rw!("and-over-or"; "(& ?x (| ?y ?z))" => "(| (& ?x ?y) (& ?x ?z))"),
        rw!("complement-law"; "(& ?x (! ?x))" => "(false)"),
        rw!("or-false"; "(| (false) ?x)" => "?x"),
    ];
    return rules;
}