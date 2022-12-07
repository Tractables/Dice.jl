#![allow(unused_variables)]
#![allow(unused_imports)]
use egg::{rewrite as rw, *};

mod dice_cg;
use dice_cg::*;

use lazy_static::lazy_static; // 1.4.0
use std::sync::Mutex;

lazy_static! {
    static ref EXPRS: Mutex<Vec<RecExpr<DiceCG>>> = Mutex::new(vec![]);
}

#[no_mangle]
pub extern fn new_expr() -> u32 {
    let mut exprs = EXPRS.lock().unwrap();
    exprs.push(RecExpr::default());
    return (exprs.len() - 1).try_into().unwrap();
}

fn get_id(id: u32) -> Id {
    let id: usize = id.try_into().unwrap();
    return id.try_into().unwrap();
}

fn give_id(id: Id) -> u32 {
    let id: usize = id.try_into().unwrap();
    return id.try_into().unwrap();
}

#[no_mangle]
pub extern fn make_or(expr_idx: u32, id1: u32, id2: u32) -> u32 {
    let id1 = get_id(id1);
    let id2 = get_id(id2);
    let expr_idx: usize = expr_idx.try_into().unwrap();
    let expr: &mut RecExpr<DiceCG> = &mut EXPRS.lock().unwrap()[expr_idx];
    return give_id(expr.add(DiceCG::Or([id1, id2])));
}