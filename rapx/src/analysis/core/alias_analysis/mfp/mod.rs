pub mod interproc;
pub mod intraproc;
pub mod transfer;

extern crate rustc_mir_dataflow;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_mir_dataflow::Analysis;
use std::cell::RefCell;
use std::rc::Rc;

use super::{AliasAnalysis, FnAliasMap, FnAliasPairs};
use crate::analysis::Analysis as RapxAnalysis;
use intraproc::FnAliasAnalyzer;

/// MFP-based alias analyzer
pub struct MfpAliasAnalyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Function summaries (alias relationships between arguments and return values)
    fn_map: FxHashMap<DefId, FnAliasPairs>,
}

impl<'tcx> MfpAliasAnalyzer<'tcx> {
    /// Create a new MFP alias analyzer
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        MfpAliasAnalyzer {
            tcx,
            fn_map: FxHashMap::default(),
        }
    }

    /// Analyze a single function
    fn analyze_function(
        &mut self,
        def_id: DefId,
        fn_summaries: &Rc<RefCell<FxHashMap<DefId, FnAliasPairs>>>,
    ) {
        let fn_name = self.tcx.def_path_str(def_id);

        // Skip functions without MIR
        if !self.tcx.is_mir_available(def_id) {
            rap_trace!("MIR not available for {:?}", fn_name);
            return;
        }

        // Skip const contexts
        if let Some(_) = self.tcx.hir_body_const_context(def_id.expect_local()) {
            rap_trace!("Skipping const context {:?}", fn_name);
            return;
        }

        rap_trace!("Analyzing function: {:?}", fn_name);

        // Get the optimized MIR
        let body = self.tcx.optimized_mir(def_id);

        // Create the intraprocedural analyzer
        let analyzer = FnAliasAnalyzer::new(self.tcx, def_id, body, fn_summaries.clone());

        // Run the dataflow analysis
        let mut results = analyzer
            .iterate_to_fixpoint(self.tcx, body, None)
            .into_results_cursor(body);

        // Extract the function summary
        let summary = interproc::extract_summary(&mut results, body, def_id);

        // Store the summary
        self.fn_map.insert(def_id, summary);
    }
}

impl<'tcx> RapxAnalysis for MfpAliasAnalyzer<'tcx> {
    fn name(&self) -> &'static str {
        "Alias Analysis (MFP)"
    }

    fn run(&mut self) {
        rap_debug!("Start alias analysis via MFP.");

        // Get all functions to analyze
        let mir_keys = self.tcx.mir_keys(());

        // Shared function summaries for interprocedural analysis
        // For now, this is empty as we're bypassing interprocedural analysis
        let fn_summaries = Rc::new(RefCell::new(FxHashMap::default()));

        // Analyze each function independently
        for local_def_id in mir_keys {
            let def_id = local_def_id.to_def_id();
            self.analyze_function(def_id, &fn_summaries);
        }

        // Sort and display results
        for (fn_id, fn_alias) in &mut self.fn_map {
            let fn_name = self.tcx.def_path_str(fn_id);
            fn_alias.sort_alias_index();
            if fn_alias.len() > 0 {
                rap_debug!("Alias found in {:?}: {}", fn_name, fn_alias);
            }
        }
    }

    fn reset(&mut self) {
        self.fn_map.clear();
    }
}

impl<'tcx> AliasAnalysis for MfpAliasAnalyzer<'tcx> {
    fn get_fn_alias(&self, def_id: DefId) -> Option<FnAliasPairs> {
        self.fn_map.get(&def_id).cloned()
    }

    fn get_all_fn_alias(&self) -> FnAliasMap {
        self.fn_map.clone()
    }
}
