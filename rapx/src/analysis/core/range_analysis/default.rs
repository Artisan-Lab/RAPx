use crate::analysis::{
    core::{
        callgraph::{default::CallGraphInfo, visitor::CallGraphVisitor},
        ownedheap_analysis::OHAResult,
        range_analysis::{
            domain::{
                domain::{ConstConvert, IntervalArithmetic, VarNodes},
                ConstraintGraph::ConstraintGraph,
            },
            Range, RangeAnalysis,
        },
        ssa_transform::*,
    },
    safedrop::graph::SafeDropGraph,
};
use crate::rap_info;

use crate::analysis::Analysis;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Place;
use rustc_middle::mir::{BasicBlock, BinOp, Body};
use rustc_middle::ty::TyCtxt;
use std::{cell::RefCell, rc::Rc};
use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
};
pub struct RangeAnalyzer<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub tcx: TyCtxt<'tcx>,
    pub debug: bool,
    pub ssa_def_id: Option<DefId>,
    pub essa_def_id: Option<DefId>,
    pub final_vars: FxHashMap<DefId, HashMap<Place<'tcx>, Range<T>>>,
    pub ssa_places_mapping: FxHashMap<DefId, HashMap<Place<'tcx>, HashSet<Place<'tcx>>>>,
    pub fn_ConstraintGraph_mapping: FxHashMap<DefId, ConstraintGraph<'tcx, T>>,
    pub callgraph: CallGraphInfo<'tcx>,
    pub body_map: FxHashMap<DefId, Body<'tcx>>,
    pub cg_map: FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
    pub vars_map: FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    pub final_vars_vec: FxHashMap<DefId, Vec<HashMap<Place<'tcx>, Range<T>>>>,
}
impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> Analysis for RangeAnalyzer<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    fn name(&self) -> &'static str {
        "Range Analysis"
    }

    fn run(&mut self) {
        // self.start();
        self.only_caller_range_analysis();
    }

    fn reset(&mut self) {
        self.final_vars.clear();
        self.ssa_places_mapping.clear();
    }
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> RangeAnalysis<'tcx, T>
    for RangeAnalyzer<'tcx, T>
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
    fn use_path_constraints_analysis(
        &self,
    ) -> (
        HashSet<BasicBlock>,
        HashMap<Vec<usize>, Vec<(Place<'tcx>, Place<'tcx>, BinOp)>>,
    ) {
        let ssa_def_id = self.ssa_def_id.expect("SSA definition ID is not set");
        let essa_def_id = self.essa_def_id.expect("ESSA definition ID is not set");
        let mut result = HashMap::new();
        let mut switchblocks: HashSet<BasicBlock> = HashSet::new();
        for local_def_id in self.tcx.iter_local_def_id() {
            if matches!(self.tcx.def_kind(local_def_id), DefKind::Fn) {
                let def_id = local_def_id.to_def_id();

                if self.tcx.is_mir_available(def_id) {
                    let mut body = self.tcx.optimized_mir(def_id).clone();
                    let body_mut_ref = unsafe { &mut *(&mut body as *mut Body<'tcx>) };

                    let mut cg: ConstraintGraph<'tcx, T> =
                        ConstraintGraph::new(def_id, essa_def_id, ssa_def_id);
                    let mut safedrop_graph =
                        SafeDropGraph::new(&body, self.tcx, def_id, OHAResult::default());
                    safedrop_graph.solve_scc();
                    let paths: Vec<Vec<usize>> = safedrop_graph.get_paths();
                    result = cg.start_analyze_path_constraints(body_mut_ref, &paths);

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
                    switchblocks = switchbbs.keys().cloned().collect();
                }
            }
        }
        return (switchblocks, result);
    }
}

impl<'tcx, T> RangeAnalyzer<'tcx, T>
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
            vars_map: FxHashMap::default(),
            final_vars_vec: FxHashMap::default(),
        }
    }

    fn build_constraintgraph(&mut self, body_mut_ref: &'tcx Body<'tcx>, def_id: DefId) {
        let ssa_def_id = self.ssa_def_id.expect("SSA definition ID is not set");
        let essa_def_id = self.essa_def_id.expect("ESSA definition ID is not set");
        let mut cg: ConstraintGraph<'tcx, T> =
            ConstraintGraph::new(def_id, essa_def_id, ssa_def_id);
        cg.build_graph(body_mut_ref);
        cg.build_nuutila(false);
        // cg.rap_print_vars();
        // cg.rap_print_final_vars();
        let vars_map = cg.get_vars().clone();

        self.cg_map.insert(def_id, Rc::new(RefCell::new(cg)));
        let mut vec = Vec::new();
        vec.push(RefCell::new(vars_map));
        self.vars_map.insert(def_id, vec);
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

                        // SSAPassRunner::print_diff(self.tcx, body_mut_ref, def_id.into());
                        // SSAPassRunner::print_mir_graph(self.tcx, body_mut_ref, def_id.into());
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

    fn only_caller_range_analysis(&mut self) {
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
                    if self.debug {
                        print_diff(self.tcx, body_mut_ref, def_id.into());
                        print_mir_graph(self.tcx, body_mut_ref, def_id.into());
                    }

                    self.ssa_places_mapping
                        .insert(def_id, passrunner.places_map.clone());
                    // rap_info!("ssa_places_mapping: {:?}", self.ssa_places_mapping);
                    // Build and store the constraint graph
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
                cg.find_intervals(&self.cg_map, &mut self.vars_map);
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
                let Some(varnodes_vec) = self.vars_map.get_mut(&def_id) else {
                    rap_info!(
                        "Warning: No VarNodes found for DefId {:?} during analysis of call chain starts.",
                        def_id
                    );
                    continue;
                };
                for varnodes in varnodes_vec.iter_mut() {
                    let ranges_for_fn_recursive = ConstraintGraph::filter_final_vars(
                        &varnodes.borrow(),
                        &self.ssa_places_mapping[&def_id],
                    );
                    self.final_vars_vec
                        .entry(def_id)
                        .or_default()
                        .push(ranges_for_fn_recursive);
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
            if let Some(var_map_vec) = self.final_vars_vec.get(&def_id) {
                rap_info!("\n--- Function: {} ---", self.tcx.def_path_str(def_id));
                for (index, var_map) in var_map_vec.iter().enumerate() {
                    if index == 0 {
                        continue;
                    }
                    rap_info!("  Final Variables (Set {}):", index);
                    if var_map.is_empty() {
                        rap_info!("  No final variables tracked for this function.");
                    } else {
                        let mut sorted_vars: Vec<_> = var_map.iter().collect();
                        sorted_vars.sort_by_key(|(place, _)| place.local.index());

                        for (place, range) in sorted_vars {
                            rap_info!("Var: {:?}, {}", place, range);
                        }
                    }
                }
            }
        }
    }
}
