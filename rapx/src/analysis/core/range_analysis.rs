#![allow(non_snake_case)]
#![allow(unused_variables)]
#![allow(dead_code)]

use crate::analysis::{
    core::{
        call_graph::{call_graph_helper::CallGraphInfo, call_graph_visitor::CallGraphVisitor},
        ownedheap_analysis::OHAResult,
        range_analysis::domain::{
            domain::{ConstConvert, IntervalArithmetic},
            range::Range,
        },
    },
    safedrop::graph::SafeDropGraph,
};
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
use std::cell::RefCell;
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
    pub cg_map: FxHashMap<DefId, RefCell<ConstraintGraph<'tcx, T>>>,
}
impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> Analysis for DefaultRange<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    fn name(&self) -> &'static str {
        "Range Analysis"
    }

    fn run(&mut self) {
        // self.start();
        self.only_caller_analyzer_mir();
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
            cg_map: FxHashMap::default(),
        }
    }

    fn build_constraintgraph(&mut self, body_mut_ref: &'tcx Body<'tcx>, def_id: DefId) {
        let ssa_def_id = self.ssa_def_id.expect("SSA definition ID is not set");
        let essa_def_id = self.essa_def_id.expect("ESSA definition ID is not set");
        let mut cg: ConstraintGraph<'tcx, T> = ConstraintGraph::new(essa_def_id, ssa_def_id);
        cg.build_graph(body_mut_ref);
        cg.build_nuutila(false);
        cg.rap_print_vars();
        cg.rap_print_final_vars();

        self.cg_map.insert(def_id, RefCell::new(cg));
    }
    fn start(&mut self) {
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
                        SSAPassRunner::print_mir_graph(self.tcx, body_mut_ref, def_id.into());
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
        // print!("{:?}", self.callgraph.get_callers_map());
        // self.callgraph.print_call_graph();
    }

    fn only_caller_analyzer_mir(&mut self) {
        let ssa_def_id = self.ssa_def_id.expect("SSA definition ID is not set");
        let essa_def_id = self.essa_def_id.expect("ESSA definition ID is not set");

        // ====================================================================
        // PHASE 1: Build all ConstraintGraphs and the complete CallGraph first.
        // ====================================================================
        rap_info!("PHASE 1: Building all ConstraintGraphs and the CallGraph...");
        for local_def_id in self.tcx.iter_local_def_id() {
            if matches!(self.tcx.def_kind(local_def_id), DefKind::Fn) {
                let def_id = local_def_id.to_def_id();

                if self.tcx.is_mir_available(def_id) {
                    let mut body = self.tcx.optimized_mir(def_id).clone();
                    let body_mut_ref = unsafe { &mut *(&mut body as *mut Body<'tcx>) };

                    // Run SSA/ESSA passes
                    let mut passrunner = PassRunner::new(self.tcx);
                    passrunner.run_pass(body_mut_ref, ssa_def_id, essa_def_id);

                    self.body_map.insert(def_id, body);
                    // Print the MIR after SSA/ESSA passes
                    SSAPassRunner::print_diff(self.tcx, body_mut_ref, def_id.into());
                    SSAPassRunner::print_mir_graph(self.tcx, body_mut_ref, def_id.into());

                    self.ssa_places_mapping
                        .insert(def_id, passrunner.places_map.clone());
                    rap_info!("ssa_places_mapping: {:?}", self.ssa_places_mapping);

                    // Bu ld and store the constraint graph
                    self.build_constraintgraph(body_mut_ref, def_id);

                    // Visit for call graph construction
                    let mut call_graph_visitor =
                        CallGraphVisitor::new(self.tcx, def_id, body_mut_ref, &mut self.callgraph);
                    call_graph_visitor.visit();
                }
            }
        }
        rap_info!("PHASE 1 Complete. CallGraph built.");
        // self.callgraph.print_call_graph(); // Optional: for debugging

        // ====================================================================
        // PHASE 2: Analyze only the call chain start functions.
        // ====================================================================
        rap_info!("PHASE 2: Finding and analyzing call chain start functions...");

        let mut call_chain_starts: Vec<DefId> = Vec::new();

        let callers_by_callee_id = self.callgraph.get_callers_map();

        for (&node_id_usize, node) in &self.callgraph.functions {
            let def_id = node.get_def_id();

            if !callers_by_callee_id.contains_key(&node_id_usize)
                && self.cg_map.contains_key(&def_id)
            {
                call_chain_starts.push(def_id);
            }
        }

        call_chain_starts.sort_by_key(|d| self.tcx.def_path_str(*d));

        rap_info!(
            "Found call chain starts ({} functions): {:?}",
            call_chain_starts.len(),
            call_chain_starts
                .iter()
                .map(|d| self.tcx.def_path_str(*d))
                .collect::<Vec<_>>()
        );

        for def_id in call_chain_starts {
            rap_info!(
                "Analyzing function (call chain start): {}",
                self.tcx.def_path_str(def_id)
            );
            if let Some(cg_cell) = self.cg_map.get(&def_id) {
                let mut cg = cg_cell.borrow_mut();
                cg.find_intervals(&self.cg_map);
            } else {
                rap_info!(
                    "Warning: No ConstraintGraph found for DefId {:?} during analysis of call chain starts.",
                    def_id
                );
            }
        }

        let analysis_order = self.callgraph.get_reverse_post_order();
        for def_id in analysis_order {
            if let Some(cg_cell) = self.cg_map.get(&def_id) {
                let mut cg = cg_cell.borrow_mut();
                let (final_vars_for_fn, _) = cg.build_final_vars(&self.ssa_places_mapping[&def_id]);
                let mut ranges_for_fn = HashMap::new();
                for (&place, varnode) in final_vars_for_fn {
                    ranges_for_fn.insert(place, varnode.get_range().clone());
                }
                self.final_vars.insert(def_id, ranges_for_fn);
            }
        }

        rap_info!("PHASE 2 Complete. Interval analysis finished for call chain start functions.");
        self.print_all_final_results();
    }
    pub fn print_all_final_results(&self) {
        rap_info!("==============================================");
        rap_info!("==== Final Analysis Results for All Functions ====");
        rap_info!("==============================================");

        if self.final_vars.is_empty() {
            rap_info!("No final results available to display.");
            rap_info!("==============================================");
            return;
        }

        let mut sorted_def_ids: Vec<DefId> = self.final_vars.keys().cloned().collect();
        sorted_def_ids.sort_by_key(|def_id| self.tcx.def_path_str(*def_id));

        for def_id in sorted_def_ids {
            if let Some(var_map) = self.final_vars.get(&def_id) {
                rap_info!("\n--- Function: {} ---", self.tcx.def_path_str(def_id));

                if var_map.is_empty() {
                    rap_info!("  No final variables tracked for this function.");
                } else {
                    for (place, range) in var_map {
                        rap_info!("Var: {:?}, {}", place, range);
                    }
                }
            }
        }
        rap_info!("\n==============================================");
    }
    pub fn using_path_constraints_analysis(&self) {
        let ssa_def_id = self.ssa_def_id.expect("SSA definition ID is not set");
        let essa_def_id = self.essa_def_id.expect("ESSA definition ID is not set");
        for local_def_id in self.tcx.iter_local_def_id() {
            if matches!(self.tcx.def_kind(local_def_id), DefKind::Fn) {
                let def_id = local_def_id.to_def_id();

                if self.tcx.is_mir_available(def_id) {
                    let mut body = self.tcx.optimized_mir(def_id).clone();
                    let body_mut_ref = unsafe { &mut *(&mut body as *mut Body<'tcx>) };

                    let mut cg: ConstraintGraph<'tcx, T> =
                        ConstraintGraph::new(essa_def_id, ssa_def_id);
                    let mut safedrop_graph =
                        SafeDropGraph::new(&body, self.tcx, def_id, OHAResult::default());
                    safedrop_graph.solve_scc();
                    let paths: Vec<Vec<usize>> = safedrop_graph.get_paths();
                    let result = cg.start_analyze_path_constraints(body_mut_ref, &paths);

                    rap_info!(
                        "SafeDropGraph Paths for function {}: {:?}",
                        self.tcx.def_path_str(def_id),
                        paths
                    );
                    let switchbbs = cg.switchbbs.clone();
                    rap_info!(
                        "Switch BBS for function {}: {:?}",
                        self.tcx.def_path_str(def_id),
                        switchbbs
                    );
                    rap_info!(
                        "Path Constraints Analysis Result for function {}: {:?}",
                        self.tcx.def_path_str(def_id),
                        result
                    );
                }
            }
        }
    }
}
