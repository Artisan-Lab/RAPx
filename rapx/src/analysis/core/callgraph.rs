pub mod default;
pub mod visitor;

use crate::Analysis;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::{fmt, collections::HashMap};

pub struct CallGraph {
    pub fn_calls: HashMap<DefId, Vec<DefId>>, // caller_id -> Vec<(callee_id)>
}

pub struct CallGraphDisplay<'a, 'tcx> {
    pub graph: &'a CallGraph,
    pub tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx> fmt::Display for CallGraphDisplay<'a, 'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "CallGraph:")?;
        for (caller, callees) in &self.graph.fn_calls {
            let caller_name = self.tcx.def_path_str(*caller);
            writeln!(f, "  {} calls:", caller_name)?;
            for callee in callees {
                let callee_name = self.tcx.def_path_str(*callee);
                writeln!(f, "    -> {}", callee_name)?;
            }
        }
        Ok(())
    }
}

pub trait CallGraphAnalysis: Analysis {
    fn get_callgraph(&mut self) -> CallGraph;
}
