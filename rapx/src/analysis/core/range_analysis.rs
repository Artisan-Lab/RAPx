#![allow(non_snake_case)]
#![allow(unused_variables)]
#![allow(dead_code)]

use crate::analysis::core::call_graph::call_graph_helper::CallGraphInfo;
use crate::analysis::core::call_graph::call_graph_visitor::CallGraphVisitor;
use crate::analysis::core::range_analysis::domain::domain::ConstConvert;
use crate::analysis::core::range_analysis::domain::domain::IntervalArithmetic;
use crate::analysis::core::range_analysis::domain::range::Range;
use crate::rap_info;

pub mod SSA;
pub mod SSAPassRunner;
pub mod domain;
use crate::analysis::Analysis;
use domain::ConstraintGraph::ConstraintGraph;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::Body;
use rustc_middle::mir::Place;
use rustc_middle::ty::TyCtxt;
use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
};
use SSAPassRunner::*;
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
            let mut passrunner = PassRunner::new(tcx);
            passrunner.run_pass(body_mut_ref, ssa_def_id, essa_def_id);
            // passrunner.print_diff(body_mut_ref);
            let essa_mir_string = passrunner.get_final_ssa_as_string(body_mut_ref);
            // rap_info!("final SSA {:?}\n", &essa_mir_string);
            rap_info!("ssa lvalue check {:?}", lvalue_check(&essa_mir_string));
        }
    }
}

pub trait RangeAnalysis<'tcx, T: IntervalArithmetic + ConstConvert + Debug>: Analysis {
    fn get_fn_range(&self, def_id: DefId) -> Option<HashMap<Place<'tcx>, Range<T>>>;
    fn get_all_fn_ranges(&self) -> FxHashMap<DefId, HashMap<Place<'tcx>, Range<T>>>;
    fn get_fn_local_range(&self, def_id: DefId, local: Place<'tcx>) -> Option<Range<T>>;
}

pub struct DefaultRange<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub tcx: TyCtxt<'tcx>,
    pub debug: bool,
    pub ssa_def_id: Option<DefId>,
    pub essa_def_id: Option<DefId>,
    pub final_vars: FxHashMap<DefId, HashMap<Place<'tcx>, Range<T>>>,
    pub ssa_places_mapping: FxHashMap<DefId, HashMap<Place<'tcx>, HashSet<Place<'tcx>>>>,
    pub fn_ConstraintGraph_mapping: FxHashMap<DefId, ConstraintGraph<'tcx, T>>,
    pub callgraph: CallGraphInfo<'tcx>,
    pub body_map: FxHashMap<DefId, Body<'tcx>>,
}
impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> Analysis for DefaultRange<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    fn name(&self) -> &'static str {
        "Range Analysis"
    }

    fn run(&mut self) {
        self.analyze_mir();
    }

    fn reset(&mut self) {
        self.final_vars.clear();
        self.ssa_places_mapping.clear();
    }
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> RangeAnalysis<'tcx, T>
    for DefaultRange<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    fn get_fn_range(&self, def_id: DefId) -> Option<HashMap<Place<'tcx>, Range<T>>> {
        self.final_vars.get(&def_id).cloned()
    }

    fn get_all_fn_ranges(&self) -> FxHashMap<DefId, HashMap<Place<'tcx>, Range<T>>> {
        // REFACTOR: Using `.clone()` is more explicit that a copy is being returned.
        self.final_vars.clone()
    }

    // REFACTOR: This lookup is now much more efficient.
    fn get_fn_local_range(&self, def_id: DefId, place: Place<'tcx>) -> Option<Range<T>> {
        self.final_vars
            .get(&def_id)
            .and_then(|vars| vars.get(&place).cloned())
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
            final_vars: FxHashMap::default(),
            ssa_places_mapping: FxHashMap::default(),
            fn_ConstraintGraph_mapping: FxHashMap::default(),
            callgraph: CallGraphInfo::new(),
            body_map: FxHashMap::default(),
        }
    }

    fn build_constraintgraph(&mut self, body_mut_ref: &'tcx Body<'tcx>, def_id: DefId) {
        let ssa_def_id = self.ssa_def_id.expect("SSA definition ID is not set");
        let essa_def_id = self.essa_def_id.expect("ESSA definition ID is not set");
        let mut cg: ConstraintGraph<'tcx, T> = ConstraintGraph::new(essa_def_id, ssa_def_id);
        cg.build_graph(body_mut_ref);
        cg.build_nuutila(false);
        cg.find_intervals();
        cg.build_final_vars(&self.ssa_places_mapping[&def_id]);
        cg.rap_print_final_vars();
        cg.test_and_print_all_symbolic_expressions();
        let mut r_final: HashMap<Place<'tcx>, Range<T>> = HashMap::default();
        let (r#final, not_found) = cg.build_final_vars(&self.ssa_places_mapping[&def_id]);

        for (&place, varnode) in r#final.iter() {
            r_final.insert(*place, varnode.get_range().clone());
        }
        self.final_vars.insert(def_id.into(), r_final);
    }
    fn analyze_mir(&mut self) {
        let ssa_def_id = self.ssa_def_id.expect("SSA definition ID is not set");
        let essa_def_id = self.essa_def_id.expect("ESSA definition ID is not set");

        for local_def_id in self.tcx.iter_local_def_id() {
            if matches!(self.tcx.def_kind(local_def_id), DefKind::Fn) {
                let def_id = local_def_id.to_def_id();

                if self.tcx.is_mir_available(def_id) {
                    rap_info!(
                        "Analyzing function: {}",
                        self.tcx.def_path_str(local_def_id)
                    );
                    let def_kind = self.tcx.def_kind(def_id);
                    let mut body = match def_kind {
                        DefKind::Const | DefKind::Static { .. } => {
                            // Compile Time Function Evaluation
                            self.tcx.mir_for_ctfe(def_id).clone()
                        }
                        _ => self.tcx.optimized_mir(def_id).clone(),
                    };
                    {
                        let body_mut_ref = unsafe { &mut *(&mut body as *mut Body<'tcx>) };

                        let mut passrunner = PassRunner::new(self.tcx);
                        passrunner.run_pass(body_mut_ref, ssa_def_id, essa_def_id);
                        self.body_map.insert(def_id.into(), body);

                        SSAPassRunner::print_diff(self.tcx, body_mut_ref, def_id.into());

                        self.ssa_places_mapping
                            .insert(def_id.into(), passrunner.places_map.clone());

                        self.build_constraintgraph(body_mut_ref, def_id.into());

                        let mut call_graph_visitor = CallGraphVisitor::new(
                            self.tcx,
                            def_id.into(),
                            body_mut_ref,
                            &mut self.callgraph,
                        );
                        call_graph_visitor.visit();
                    }
                }
            }
        }
        print!("{:?}", self.callgraph.get_callers_map());
        // print!("{:?}", self.body_map);
        self.callgraph.print_call_graph();
    }
}
