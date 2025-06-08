pub mod alias;
pub mod bug_records;
pub mod check_bugs;
pub mod corner_handle;
pub mod graph;
#[allow(clippy::module_inception)]
pub mod safedrop;
pub mod types;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::analysis::core::alias::mop::MopAlias;
use crate::analysis::core::alias::FnMap;
use crate::analysis::core::heap_item::{AdtOwner, TypeAnalysis};
use crate::analysis::rcanary::rCanary;
use graph::SafeDropGraph;
use safedrop::*;

pub struct SafeDrop<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> SafeDrop<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }
    pub fn start(&self) {
        let mut mop = MopAlias::new(self.tcx);
        let fn_map = mop.start();

        let rcx_boxed = Box::new(rCanary::new(self.tcx));
        let rcx = Box::leak(rcx_boxed);
        TypeAnalysis::new(rcx).start();

        let mir_keys = self.tcx.mir_keys(());
        for local_def_id in mir_keys {
            query_safedrop(
                self.tcx,
                fn_map,
                local_def_id.to_def_id(),
                rcx.adt_owner().clone(),
            );
        }
    }
}

pub fn query_safedrop(tcx: TyCtxt, fn_map: &FnMap, def_id: DefId, adt_owner: AdtOwner) {
    /* filter const mir */
    if let Some(_other) = tcx.hir_body_const_context(def_id.expect_local()) {
        return;
    }
    if tcx.is_mir_available(def_id) {
        let body = tcx.optimized_mir(def_id);
        let mut safedrop_graph = SafeDropGraph::new(body, tcx, def_id, adt_owner);
        safedrop_graph.solve_scc();
        safedrop_graph.check(0, tcx, fn_map);
        if safedrop_graph.visit_times <= VISIT_LIMIT {
            safedrop_graph.report_bugs();
        } else {
            println!("Over visited: {:?}", def_id);
        }
    }
}
