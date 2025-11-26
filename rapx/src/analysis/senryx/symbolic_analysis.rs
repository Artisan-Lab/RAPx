// use std::collections::HashMap;

use rustc_middle::mir::{BinOp, UnOp};
// use z3::ast::{Ast, BV, Bool};
// use z3::{Config, Context, SatResult, Solver};

// use crate::analysis::senryx::visitor::BodyVisitor;

#[derive(Clone, Debug)]
pub enum SymbolicDef {
    Param(usize),
    Constant(u128),
    Use(usize),
    Cast(usize, String),
    Binary(BinOp, usize, AnaOperand),
    UnOp(UnOp),
    Call(String, Vec<usize>),
    Ref(usize),
}

#[derive(Clone, Debug)]
pub enum AnaOperand {
    Local(usize),
    Const(u128),
}

#[derive(Clone, Debug, Default)]
pub struct ValueDomain {
    pub def: Option<SymbolicDef>,
    pub value_constraint: Option<u128>,
    pub align: Option<(u64, u64)>,
}

// impl<'tcx> BodyVisitor<'tcx> {
//     fn get_operand_bv(&'tcx self, ctx: &Context, op: &AnaOperand, z3_vars: &'tcx HashMap<usize, BV>) -> Option<BV> {
//         match op {
//             AnaOperand::Local(idx) => z3_vars.get(idx).cloned(),
//             AnaOperand::Const(val) => Some(BV::from_u64(ctx, *val as u64, 64)),
//         }
//     }

//     pub fn verify_with_z3<F>(&'tcx self, target_verifier: F) -> bool
//     where
//         F: FnOnce(&'tcx Context, &'tcx HashMap<usize, BV>) -> Bool<'tcx>
//     {
//         let cfg = Config::new();
//         let ctx = Context::new(&cfg);
//         let solver = Solver::new(&ctx);

//         let mut z3_vars: HashMap<usize, BV> = HashMap::new();

//         for local_index in self.value_domains.keys() {
//             let name = format!("loc_{}", local_index);
//             z3_vars.insert(*local_index, BV::new_const(&ctx, name, 64));
//         }

//         for (local_idx, domain) in &self.value_domains {
//             let current_var = match z3_vars.get(local_idx) {
//                 Some(v) => v,
//                 None => continue,
//             };

//             if let Some(ref def) = domain.def {
//                 match def {
//                     SymbolicDef::Call(name, args) if name.contains("byte_add") && args.len() == 2 => {
//                         if let (Some(lhs), Some(rhs)) = (z3_vars.get(&args[0]), z3_vars.get(&args[1])) {
//                             solver.assert(&current_var._eq(&lhs.bvadd(rhs)));
//                         }
//                     },
//                     SymbolicDef::Cast(src_idx, _) => {
//                          if let Some(src_var) = z3_vars.get(src_idx) {
//                             solver.assert(&current_var._eq(src_var));
//                          }
//                     },
//                     SymbolicDef::Binary(op, lhs_idx, rhs_op) => {
//                         if let (Some(lhs), Some(rhs)) = (z3_vars.get(lhs_idx), self.get_operand_bv(&ctx, rhs_op, &z3_vars)) {
//                             let result_expr = match op {
//                                 BinOp::Rem => lhs.bvurem(&rhs),
//                                 BinOp::Eq => lhs._eq(&rhs).ite(&BV::from_u64(&ctx, 1, 64), &BV::from_u64(&ctx, 0, 64)),
//                                 BinOp::Add => lhs.bvadd(&rhs),
//                                 _ => continue,
//                             };
//                             solver.assert(&current_var._eq(&result_expr));
//                         }
//                     },
//                     SymbolicDef::Use(src_idx) => {
//                          if let Some(src_var) = z3_vars.get(src_idx) {
//                             solver.assert(&current_var._eq(src_var));
//                          }
//                     }
//                     _ => {}
//                 }
//             }
//             if let Some(val) = domain.value_constraint {
//                 let z3_val = BV::from_u64(&ctx, val as u64, 64);
//                 solver.assert(&current_var._eq(&z3_val));
//             }
//         }

//         let target_prop = target_verifier(&ctx, &z3_vars);
//         solver.assert(&target_prop.not());

//         match solver.check() {
//             SatResult::Unsat => true,
//             _ => false,
//         }
//     }

//     pub fn verify_alignment(&self, local_idx: usize, required_align: u64) -> bool {
//         self.verify_with_z3(|ctx, vars| {
//             if let Some(var) = vars.get(&local_idx) {
//                 let z3_align = BV::from_u64(ctx, required_align, 64);
//                 let zero = BV::from_u64(ctx, 0, 64);
//                 var.bvurem(&z3_align)._eq(&zero)
//             } else {
//                 Bool::from_bool(ctx, false)
//             }
//         })
//     }
// }
