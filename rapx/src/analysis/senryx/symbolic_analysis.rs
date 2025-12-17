use rustc_middle::mir::{BinOp, UnOp};
use std::collections::HashMap;

use z3::ast::{Ast, BV, Bool};
use z3::{Config, Context, SatResult, Solver};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SymbolicDef {
    Param(usize),
    Constant(u128),
    Use(usize),
    Cast(usize, String),
    Binary(BinOp, usize, AnaOperand),
    UnOp(UnOp),
    Call(String, Vec<AnaOperand>),
    Ref(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnaOperand {
    Local(usize),
    Const(u128),
}

#[derive(Clone, Debug, Default)]
pub struct ValueDomain {
    pub def: Option<SymbolicDef>,
    pub value_constraint: Option<u128>,
}

impl ValueDomain {
    pub fn get_constant(&self) -> Option<u128> {
        if let Some(SymbolicDef::Constant(c)) = self.def {
            Some(c)
        } else {
            self.value_constraint
        }
    }
}

/// Verifies a target property using Z3 SMT solver given variable domains and path constraints.
/// Returns true if the property holds (UNSAT for negation), false otherwise.
pub fn verify_with_z3<F>(
    values: HashMap<usize, ValueDomain>,
    path_constraints: Vec<SymbolicDef>,
    target_verifier: F,
) -> bool
where
    F: for<'ctx> FnOnce(&'ctx Context, &HashMap<usize, BV<'ctx>>) -> Bool<'ctx>,
{
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let mut z3_vars: HashMap<usize, BV> = HashMap::new();

    // Create symbolic bitvector variables for all locals
    for local_index in values.keys() {
        let name = format!("loc_{}", local_index);
        z3_vars.insert(*local_index, BV::new_const(&ctx, name, 64));
    }

    // Encode variable definitions (assignments, operations) as solver constraints
    for (local_idx, domain) in &values {
        let current_var = match z3_vars.get(local_idx) {
            Some(v) => v,
            None => continue,
        };

        if let Some(ref def) = domain.def {
            match def {
                // SymbolicDef::Call(name, args) if name.contains("byte_add") && args.len() == 2 => {
                //     if let (Some(lhs), Some(rhs)) = (z3_vars.get(&args[0]), z3_vars.get(&args[1])) {
                //         solver.assert(&current_var._eq(&lhs.bvadd(rhs)));
                //     }
                // }
                SymbolicDef::Cast(src_idx, _) => {
                    if let Some(src_var) = z3_vars.get(src_idx) {
                        solver.assert(&current_var._eq(src_var));
                    }
                }
                SymbolicDef::Binary(op, lhs_idx, rhs_op) => {
                    if let (Some(lhs), Some(rhs)) =
                        (z3_vars.get(lhs_idx), get_operand_bv(&ctx, rhs_op, &z3_vars))
                    {
                        let result_expr = match op {
                            BinOp::Rem => lhs.bvurem(&rhs),
                            BinOp::Eq => lhs
                                ._eq(&rhs)
                                .ite(&BV::from_u64(&ctx, 1, 64), &BV::from_u64(&ctx, 0, 64)),
                            BinOp::Add => lhs.bvadd(&rhs),
                            _ => continue,
                        };
                        solver.assert(&current_var._eq(&result_expr));
                    }
                }
                SymbolicDef::Use(src_idx) => {
                    if let Some(src_var) = z3_vars.get(src_idx) {
                        solver.assert(&current_var._eq(src_var));
                    }
                }
                _ => {}
            }
        }
        if let Some(val) = domain.value_constraint {
            let z3_val = BV::from_u64(&ctx, val as u64, 64);
            solver.assert(&current_var._eq(&z3_val));
        }
    }

    // Apply path constraints (e.g., branch conditions)
    for constraint in path_constraints {
        match constraint {
            SymbolicDef::Binary(op, lhs_idx, rhs_op) => {
                if let (Some(lhs), Some(rhs)) = (
                    z3_vars.get(&lhs_idx),
                    get_operand_bv(&ctx, &rhs_op, &z3_vars),
                ) {
                    match op {
                        BinOp::Eq => solver.assert(&lhs._eq(&rhs)),
                        BinOp::Ne => solver.assert(&lhs._eq(&rhs).not()),
                        BinOp::Lt => solver.assert(&lhs.bvult(&rhs)),
                        BinOp::Gt => solver.assert(&rhs.bvult(&lhs)),
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    // Assert negation of the target property
    let target_prop = target_verifier(&ctx, &z3_vars);
    solver.assert(&target_prop.not());

    // Check satisfiability
    let result = solver.check();

    // Debug output: Inspect solver state and model if needed
    debug_z3_solver_state(&solver, result, &z3_vars);

    // UNSAT means no counter-example exists -> property holds
    match result {
        SatResult::Unsat => true,
        _ => false,
    }
}

// Helper function to handle Z3 solver debug outputs
fn debug_z3_solver_state<'ctx>(
    solver: &Solver<'ctx>,
    result: SatResult,
    z3_vars: &HashMap<usize, BV<'ctx>>,
) {
    // Log the raw SMT-LIB constraints for inspection
    rap_info!("[Z3 Verify] Constraints:\n{}", solver);

    match result {
        SatResult::Unsat => {
            rap_info!("[Z3 Verify] Result: UNSAT (Verification Passed)");
        }
        SatResult::Sat => {
            rap_info!("[Z3 Verify] Result: SAT (Verification Failed)");

            // Attempt to retrieve and display the counter-example model
            if let Some(model) = solver.get_model() {
                rap_info!("[Z3 Verify] Model:\n{}", model);

                // Extract and log specific values for variables in the model
                let mut sorted_vars: Vec<_> = z3_vars.iter().collect();
                sorted_vars.sort_by_key(|k| k.0);

                for (idx, bv) in sorted_vars {
                    if let Some(interp) = model.eval(bv, true) {
                        let val_str = interp
                            .as_u64()
                            .map(|v| v.to_string())
                            .unwrap_or_else(|| interp.to_string());
                        rap_info!("  loc_{}: {}", idx, val_str);
                    }
                }
            }
        }
        SatResult::Unknown => {
            let reason = solver
                .get_reason_unknown()
                .unwrap_or_else(|| "Unknown".to_string());
            rap_info!("[Z3 Verify] Result: UNKNOWN. Reason: {}", reason);
        }
    }
}

fn get_operand_bv<'a>(
    ctx: &'a Context,
    op: &'a AnaOperand,
    z3_vars: &'a HashMap<usize, BV>,
) -> Option<BV<'a>> {
    match op {
        AnaOperand::Local(idx) => z3_vars.get(idx).cloned(),
        AnaOperand::Const(val) => Some(BV::from_u64(ctx, *val as u64, 64)),
    }
}
