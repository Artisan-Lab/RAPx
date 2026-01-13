pub mod interproc;
pub mod intraproc;
pub mod transfer;

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::cell::RefCell;
use std::rc::Rc;

use super::{AliasAnalysis, FnAliasMap, FnAliasPairs};
use crate::analysis::Analysis;
use intraproc::{FnAliasAnalyzer, PlaceInfo};

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
}

impl<'tcx> Analysis for MfpAliasAnalyzer<'tcx> {
    fn name(&self) -> &'static str {
        "Alias Analysis (MFP)"
    }

    fn run(&mut self) {
        // TODO: Implement fixpoint iteration
        // 1. Collect all functions
        // 2. Initialize summaries
        // 3. Iterate until fixpoint
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
