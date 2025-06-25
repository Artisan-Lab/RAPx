#![allow(non_snake_case)]
#![allow(unused_variables)]
#![allow(dead_code)]

use crate::analysis::core::range_analysis::domain::domain::ConstConvert;
use crate::analysis::core::range_analysis::domain::domain::IntervalArithmetic;
use crate::analysis::core::range_analysis::domain::range::Range;
use crate::rap_info;

pub mod PassRunner;
pub mod SSA;
pub mod domain;
use crate::analysis::Analysis;
use domain::ConstraintGraph::ConstraintGraph;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::Body;
use rustc_middle::mir::Local;
use rustc_middle::ty::TyCtxt;
use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
};
use PassRunner::*;
pub struct SSATrans<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub debug: bool,
}

impl<'tcx> SSATrans<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, debug: bool) -> Self {
        Self { tcx: tcx, debug }
    }

    pub fn start(&mut self) {
        for local_def_id in self.tcx.iter_local_def_id() {
            if matches!(self.tcx.def_kind(local_def_id), DefKind::Fn) {
                if self.tcx.hir_maybe_body_owned_by(local_def_id).is_some() {
                    if let Some(def_id) = self
                        .tcx
                        .hir_body_owners()
                        .find(|id| self.tcx.def_path_str(*id) == "main")
                    {
                        if let Some(ssa_def_id) =
                            self.tcx.hir_crate_items(()).free_items().find(|id| {
                                let hir_id = id.hir_id();
                                if let Some(ident_name) = self.tcx.hir_opt_name(hir_id) {
                                    ident_name.to_string() == "SSAstmt"
                                } else {
                                    false
                                }
                            })
                        {
                            let ssa_def_id = ssa_def_id.owner_id.to_def_id();
                            if let Some(essa_def_id) =
                                self.tcx.hir_crate_items(()).free_items().find(|id| {
                                    let hir_id = id.hir_id();
                                    if let Some(ident_name) = self.tcx.hir_opt_name(hir_id) {
                                        ident_name.to_string() == "ESSAstmt"
                                    } else {
                                        false
                                    }
                                })
                            {
                                let essa_def_id = essa_def_id.owner_id.to_def_id();
                                self.analyze_mir(self.tcx, def_id, ssa_def_id, essa_def_id);
                            }
                        }
                    }
                }
            }
        }
    }
    fn analyze_mir(
        &mut self,
        tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
        ssa_def_id: DefId,
        essa_def_id: DefId,
    ) {
        let mut body = tcx.optimized_mir(def_id).clone();
        {
            let body_mut_ref: &mut Body<'tcx> = unsafe { &mut *(&mut body as *mut Body<'tcx>) };
            let mut passrunner = PassRunner::PassRunner::new(tcx);
            passrunner.run_pass(body_mut_ref, ssa_def_id, essa_def_id);
            // passrunner.print_diff(body_mut_ref);
            let essa_mir_string = passrunner.get_final_ssa_as_string(body_mut_ref);
            // rap_info!("final SSA {:?}\n", &essa_mir_string);
            rap_info!("ssa lvalue check {:?}", lvalue_check(&essa_mir_string));
        }
    }
}

pub trait RangeAnalysis<'tcx, T: IntervalArithmetic + ConstConvert + Debug>: Analysis {
    fn get_fn_range(&self, def_id: DefId) -> Option<HashMap<Local, Range<T>>>;
    fn get_all_fn_ranges(&self) -> FxHashMap<DefId, HashMap<Local, Range<T>>>;
    fn get_fn_local_range(&self, def_id: DefId, local: Local) -> Option<Range<T>>;
}

pub struct DefaultRange<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub tcx: TyCtxt<'tcx>,
    pub debug: bool,
    pub ssa_def_id: Option<DefId>,
    pub essa_def_id: Option<DefId>,
    pub final_vars: FxHashMap<DefId, HashMap<Local, Range<T>>>,
    pub ssa_locals_mapping: FxHashMap<DefId, HashMap<Local, HashSet<Local>>>,
}
impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> Analysis for DefaultRange<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    fn name(&self) -> &'static str {
        "Range Analysis"
    }

    fn run(&mut self) {
        for local_def_id in self.tcx.iter_local_def_id() {
            if matches!(self.tcx.def_kind(local_def_id), DefKind::Fn) {
                if self.tcx.hir_maybe_body_owned_by(local_def_id).is_some() {
                    rap_info!(
                        "Analyzing function: {}",
                        self.tcx.def_path_str(local_def_id)
                    );
                    self.analyze_mir(local_def_id);
                }
            }
        }
    }

    fn reset(&mut self) {
        self.final_vars.clear();
        self.ssa_locals_mapping.clear();
    }
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> RangeAnalysis<'tcx, T>
    for DefaultRange<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    fn get_fn_range(&self, def_id: DefId) -> Option<HashMap<Local, Range<T>>> {
        self.final_vars.get(&def_id).cloned()
    }

    fn get_all_fn_ranges(&self) -> FxHashMap<DefId, HashMap<Local, Range<T>>> {
        // REFACTOR: Using `.clone()` is more explicit that a copy is being returned.
        self.final_vars.clone()
    }

    // REFACTOR: This lookup is now much more efficient.
    fn get_fn_local_range(&self, def_id: DefId, local: Local) -> Option<Range<T>> {
        self.final_vars
            .get(&def_id)
            .and_then(|vars| vars.get(&local).cloned())
    }
}

impl<'tcx, T> DefaultRange<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    pub fn new(tcx: TyCtxt<'tcx>, debug: bool) -> Self {
        let mut ssa_id = None;
        let mut essa_id = None;

        if let Some(ssa_def_id) = tcx.hir_crate_items(()).free_items().find(|id| {
            let hir_id = id.hir_id();
            if let Some(ident_name) = tcx.hir_opt_name(hir_id) {
                ident_name.to_string() == "SSAstmt"
            } else {
                false
            }
        }) {
            ssa_id = Some(ssa_def_id.owner_id.to_def_id());
            if let Some(essa_def_id) = tcx.hir_crate_items(()).free_items().find(|id| {
                let hir_id = id.hir_id();
                if let Some(ident_name) = tcx.hir_opt_name(hir_id) {
                    ident_name.to_string() == "ESSAstmt"
                } else {
                    false
                }
            }) {
                essa_id = Some(essa_def_id.owner_id.to_def_id());
            }
        }
        Self {
            tcx: tcx,
            debug,
            ssa_def_id: ssa_id,
            essa_def_id: essa_id,
            final_vars: HashMap::default(),
            ssa_locals_mapping: HashMap::default(),
        }
    }

    fn analyze_mir(&mut self, def_id: LocalDefId) {
        let mut body = self.tcx.optimized_mir(def_id).clone();
        {
            let ssa_def_id = self.ssa_def_id.expect("SSA definition ID is not set");
            let essa_def_id = self.essa_def_id.expect("ESSA definition ID is not set");

            let body_mut_ref: &mut Body<'tcx> = unsafe { &mut *(&mut body as *mut Body<'tcx>) };
            let mut passrunner = PassRunner::PassRunner::new(self.tcx);
            passrunner.run_pass(body_mut_ref, ssa_def_id, essa_def_id);
            // print_diff(tcx, body_mut_ref);
            let mut cg: ConstraintGraph<'tcx, T> = ConstraintGraph::new(essa_def_id, ssa_def_id);
            cg.build_graph(body_mut_ref);
            cg.build_nuutila(false);
            cg.find_intervals();
            cg.rap_print_vars();
            let (r#final, not_found) = cg.build_final_vars(&passrunner.locals_map);
            cg.rap_print_final_vars();

            self.ssa_locals_mapping
                .insert(def_id.into(), passrunner.locals_map.clone());

            let mut r_final = HashMap::default();

            for (&place, varnode) in r#final.iter() {
                r_final.insert(place.local, varnode.get_range().clone());
            }
            self.final_vars.insert(def_id.into(), r_final);
        }
    }
}
