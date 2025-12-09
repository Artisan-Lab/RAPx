/*
 * This module generates the unsafety propagation graph for each Rust module in the target crate.
 */
pub mod fn_collector;
pub mod hir_visitor;
pub mod render_module_dot;
pub mod std_upg;
pub mod upg_unit;

use crate::{
    utils::source::get_fn_name_byid,
    analysis::utils::{draw_dot::render_dot_graphs, fn_info::*},
};
use fn_collector::FnCollector;
use hir_visitor::ContainsUnsafe;
use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::{mir::Local, ty::TyCtxt};
use std::collections::HashSet;
use upg_unit::UPGUnit;

#[derive(PartialEq)]
pub enum TargetCrate {
    Std,
    Other,
}

pub struct UPGAnalysis<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub upgs: Vec<UPGUnit>,
}

impl<'tcx> UPGAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            upgs: Vec::new(),
        }
    }

    pub fn start(&mut self, ins: TargetCrate) {
        match ins {
            TargetCrate::Std => {
                self.audit_std_unsafe();
                return;
            }
            _ => {
                /* Type of collected data: FxHashMap<Option<HirId>, Vec<(BodyId, Span)>>;
                 * For a function, the Vec contains only one entry;
                 * For implementations of structs and traits, the Vec contains all associated
                 * function entries.
                 */
                let fns = FnCollector::collect(self.tcx);
                for vec in fns.values() {
                    for (body_id, _span) in vec {
                        // each function or associated function in
                        // structs and traits
                        let (fn_unsafe, block_unsafe) =
                            ContainsUnsafe::contains_unsafe(self.tcx, *body_id);
                        // map the function body_id back to its def_id;
                        let def_id = self.tcx.hir_body_owner_def_id(*body_id).to_def_id();
                        if fn_unsafe | block_unsafe {
                            self.insert_upg(def_id);
                        }
                    }
                }
                self.render_module_dot();
            }
        }
    }

    pub fn render_dot(&mut self) {
        let mut dot_strs = Vec::new();
        for upg in &self.upgs {
            let dot_str = upg.generate_dot_str();
            let caller_name = get_cleaned_def_path_name(self.tcx, upg.caller.def_id);
            dot_strs.push((caller_name, dot_str));
        }
        render_dot_graphs(dot_strs);
    }

    pub fn insert_upg(&mut self, def_id: DefId) {
        let callees = get_unsafe_callees(self.tcx, def_id);
        let raw_ptrs = get_rawptr_deref(self.tcx, def_id);
        let global_locals = collect_global_local_pairs(self.tcx, def_id);
        let static_muts: HashSet<DefId> = global_locals.keys().copied().collect();

        /*Static mutable access is in nature via raw ptr; We have to prune the duplication.*/
        let global_locals_set: HashSet<Local> = global_locals.values().flatten().copied().collect();
        let raw_ptrs_filtered: HashSet<Local> =
            raw_ptrs.difference(&global_locals_set).copied().collect();

        let constructors = get_cons(self.tcx, def_id);
        let caller_typed = append_fn_with_types(self.tcx, def_id);
        let mut callees_typed = HashSet::new();
        for callee in &callees {
            callees_typed.insert(append_fn_with_types(self.tcx, *callee));
        }
        let mut cons_typed = HashSet::new();
        for con in &constructors {
            cons_typed.insert(append_fn_with_types(self.tcx, *con));
        }

        // Skip processing if the caller is the dummy raw pointer dereference function
        let caller_name = get_fn_name_byid(&def_id);
        if let Some(_) = caller_name.find("__raw_ptr_deref_dummy") {
            return;
        }

        // If the function is entirely safe (no unsafe code, no unsafe callees, no raw pointer dereferences, and no static mutable accesses), skip further analysis
        if check_safety(self.tcx, def_id) == Safety::Safe
            && callees.is_empty()
            && raw_ptrs.is_empty()
            && static_muts.is_empty()
        {
            return;
        }
        let mut_methods_set = get_all_mutable_methods(self.tcx, def_id);
        let mut_methods = mut_methods_set.keys().copied().collect();
        let upg = UPGUnit::new(
            caller_typed,
            callees_typed,
            raw_ptrs_filtered,
            static_muts,
            cons_typed,
            mut_methods,
        );
        self.upgs.push(upg);
    }
}
