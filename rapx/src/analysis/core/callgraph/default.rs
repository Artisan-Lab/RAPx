use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{self, Body},
    ty::TyCtxt,
};
use std::collections::HashMap;
use std::collections::HashSet;

use super::visitor::CallGraphVisitor;
use crate::{
    Analysis,
    analysis::core::callgraph::{CallGraphAnalysis, FnCallMap},
};

pub struct CallGraphAnalyzer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub graph: CallGraph<'tcx>,
}

impl<'tcx> Analysis for CallGraphAnalyzer<'tcx> {
    fn name(&self) -> &'static str {
        "Default call graph analysis algorithm."
    }

    fn run(&mut self) {
        self.start();
    }

    fn reset(&mut self) {
        todo!();
    }
}

impl<'tcx> CallGraphAnalysis for CallGraphAnalyzer<'tcx> {
    fn get_fn_calls(&self) -> FnCallMap {
        let fn_calls: HashMap<DefId, Vec<DefId>> = self
            .graph
            .fn_calls
            .clone()
            .into_iter()
            .map(|(caller, callees)| {
                let callee_ids = callees.into_iter().map(|(did, _)| did).collect::<Vec<_>>();
                (caller, callee_ids)
            })
            .collect();
        fn_calls
    }
}

impl<'tcx> CallGraphAnalyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx: tcx,
            graph: CallGraph::new(tcx),
        }
    }

    pub fn start(&mut self) {
        for local_def_id in self.tcx.iter_local_def_id() {
            if self.tcx.hir_maybe_body_owned_by(local_def_id).is_some() {
                let def_id = local_def_id.to_def_id();
                if self.tcx.is_mir_available(def_id) {
                    let def_kind = self.tcx.def_kind(def_id);

                    let body: &Body<'_> = match def_kind {
                        DefKind::Fn | DefKind::AssocFn => &self.tcx.optimized_mir(def_id),
                        DefKind::Const
                        | DefKind::Static { .. }
                        | DefKind::AssocConst
                        | DefKind::InlineConst
                        | DefKind::AnonConst => {
                            // NOTE: safer fallback for constants
                            &self.tcx.mir_for_ctfe(def_id)
                        }
                        // These don't have MIR or shouldn't be visited
                        _ => {
                            rap_debug!("Skipping def_id {:?} with kind {:?}", def_id, def_kind);
                            continue;
                        }
                    };

                    let mut call_graph_visitor =
                        CallGraphVisitor::new(self.tcx, def_id.into(), body, &mut self.graph);
                    call_graph_visitor.visit();
                }
            }
        }
    }
}

pub type CallMap<'tcx> = HashMap<DefId, Vec<(DefId, Option<&'tcx mir::Terminator<'tcx>>)>>;

pub struct CallGraph<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub functions: HashSet<DefId>, // Function-like, including closures
    pub fn_calls: CallMap<'tcx>,   // caller -> Vec<(callee, terminator)>
}

impl<'tcx> CallGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            functions: HashSet::new(),
            fn_calls: HashMap::new(),
        }
    }

    /// Register a function to the call graph. Return true on insert, false if that DefId already exists.
    pub fn register_fn(&mut self, def_id: DefId) -> bool {
        if let Some(_) = self.functions.iter().find(|func_id| **func_id == def_id) {
            false
        } else {
            self.functions.insert(def_id);
            true
        }
    }

    /// Add a function call to the call graph.
    pub fn add_funciton_call(
        &mut self,
        caller_id: DefId,
        callee_id: DefId,
        terminator_stmt: Option<&'tcx mir::Terminator<'tcx>>,
    ) {
        let entry = self.fn_calls.entry(caller_id).or_insert_with(Vec::new);
        entry.push((callee_id, terminator_stmt));
    }

    /// Get a reversed (callee -> Vec<Caller>) call map.
    pub fn get_callers_map(&self) -> CallMap<'tcx> {
        let mut callers_map: CallMap<'tcx> = HashMap::new();

        for (&caller_id, calls_vec) in &self.fn_calls {
            for (callee_id, terminator) in calls_vec {
                callers_map
                    .entry(*callee_id)
                    .or_insert_with(Vec::new)
                    .push((caller_id, *terminator));
            }
        }
        callers_map
    }

    pub fn get_reverse_post_order(&self) -> Vec<DefId> {
        let mut visited = HashSet::new();
        let mut post_order_ids = Vec::new(); // Will store the post-order traversal of `usize` IDs

        // Iterate over all functions defined in the graph to handle disconnected components
        for &func_def_id in self.functions.iter() {
            if !visited.contains(&func_def_id) {
                self.dfs_post_order(func_def_id, &mut visited, &mut post_order_ids);
            }
        }

        // Map the ordered `usize` IDs back to `DefId`s for the analysis pipeline
        let mut analysis_order: Vec<DefId> = post_order_ids;

        // Reversing the post-order gives a topological sort (bottom-up)
        analysis_order.reverse();

        analysis_order
    }

    /// Helper function to perform a recursive depth-first search.
    fn dfs_post_order(
        &self,
        func_def_id: DefId,
        visited: &mut HashSet<DefId>,
        post_order_ids: &mut Vec<DefId>,
    ) {
        // Mark the current node as visited
        visited.insert(func_def_id);

        // Visit all callees (children) of the current node
        if let Some(callees) = self.fn_calls.get(&func_def_id) {
            for (callee_id, _terminator) in callees {
                if !visited.contains(callee_id) {
                    self.dfs_post_order(*callee_id, visited, post_order_ids);
                }
            }
        }

        // After visiting all children, add the current node to the post-order list
        post_order_ids.push(func_def_id);
    }
}
