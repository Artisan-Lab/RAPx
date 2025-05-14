pub mod alias;
pub mod graph;
pub mod mop;
pub mod types;

use crate::analysis::core::alias::{FnMap, RetAlias};
use crate::analysis::utils::intrinsic_id::{
    COPY_FROM, COPY_FROM_NONOVERLAPPING, COPY_TO, COPY_TO_NONOVERLAPPING,
};
use crate::utils::source::*;
use crate::{rap_debug, rap_info, rap_trace};
use graph::MopGraph;
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use std::collections::HashSet;

pub const VISIT_LIMIT: usize = 100;

pub struct MopAlias<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub fn_map: FnMap,
}

impl<'tcx> MopAlias<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            fn_map: FxHashMap::default(),
        }
    }

    pub fn start(&mut self) -> &FnMap {
        rap_debug!("Start alias analysis via MoP.");
        for local_def_id in self.tcx.iter_local_def_id() {
            let hir_map = self.tcx.hir();
            if hir_map.maybe_body_owned_by(local_def_id).is_some() {
                self.query_mop(local_def_id.to_def_id());
            }
        }
        // Meaning of output: 0 for ret value; 1,2,3,... for corresponding args.
        for (fn_id, fn_alias) in &mut self.fn_map {
            let fn_name = get_fn_name(self.tcx, *fn_id);
            fn_alias.sort_alias_index();
            if fn_alias.len() > 0 {
                rap_info!("Alias found in {:?}: {}", fn_name, fn_alias);
            }
        }
        self.handle_conor_cases();
        &self.fn_map
    }

    pub fn handle_conor_cases(&mut self) {
        let cases = [
            COPY_FROM_NONOVERLAPPING,
            COPY_TO_NONOVERLAPPING,
            COPY_TO,
            COPY_FROM,
        ];
        let alias = RetAlias::new(1, true, true, 2, true, true);
        for (key, value) in self.fn_map.iter_mut() {
            if cases.contains(&key.index.as_usize()) {
                value.alias_set.clear();
                value.alias_set.insert(alias.clone());
            }
        }
    }

    pub fn query_mop(&mut self, def_id: DefId) {
        let fn_name = get_fn_name(self.tcx, def_id);
        rap_trace!("query_mop: {:?}", fn_name);
        /* filter const mir */
        if let Some(_other) = self.tcx.hir().body_const_context(def_id.expect_local()) {
            return;
        }

        if self.tcx.is_mir_available(def_id) {
            let mut mop_graph = MopGraph::new(self.tcx, def_id);
            mop_graph.solve_scc();
            let mut recursion_set = HashSet::default();
            mop_graph.check(0, &mut self.fn_map, &mut recursion_set);
            if mop_graph.visit_times > VISIT_LIMIT {
                rap_trace!("Over visited: {:?}", def_id);
            }
            self.fn_map.insert(def_id, mop_graph.ret_alias);
        } else {
            rap_trace!("mir is not available at {}", self.tcx.def_path_str(def_id));
        }
    }
}
