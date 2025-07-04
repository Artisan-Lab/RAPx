pub mod alias;
pub mod graph;
pub mod mop;

use super::{AAFact, AAResult, AliasAnalysis};
use crate::{
    analysis::{
        utils::intrinsic_id::{
            COPY_FROM, COPY_FROM_NONOVERLAPPING, COPY_TO, COPY_TO_NONOVERLAPPING,
        },
        Analysis,
    },
    rap_debug, rap_info, rap_trace,
    utils::source::*,
};
use graph::MopGraph;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::{collections::HashSet, convert::From};

pub const VISIT_LIMIT: usize = 1000;

pub struct DefaultAlias<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub fn_map: FxHashMap<DefId, AAResult>,
}

impl<'tcx> Analysis for DefaultAlias<'tcx> {
    fn name(&self) -> &'static str {
        "Default alias analysis algorithm."
    }

    fn run(&mut self) {
        rap_debug!("Start alias analysis.");
        let mir_keys = self.tcx.mir_keys(());
        for local_def_id in mir_keys {
            self.query_mop(local_def_id.to_def_id());
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
    }

    fn reset(&mut self) {
        todo!();
    }
}

impl<'tcx, T> AliasAnalysis<T> for DefaultAlias<'tcx>
where
    T: From<AAResult> + Clone,
{
    fn get_fn_alias(&mut self, def_id: DefId) -> T {
        self.fn_map
            .get(&def_id)
            .expect(&format!("Cannot find alias analysis result for {def_id:?}"))
            .clone()
            .into()
    }

    fn get_all_fn_alias(&mut self) -> FxHashMap<DefId, T> {
        self.fn_map
            .iter()
            .map(|(k, v)| (*k, T::from(v.clone())))
            .collect::<FxHashMap<DefId, T>>()
    }
}

impl<'tcx> DefaultAlias<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            fn_map: FxHashMap::default(),
        }
    }

    fn handle_conor_cases(&mut self) {
        let cases = [
            COPY_FROM_NONOVERLAPPING,
            COPY_TO_NONOVERLAPPING,
            COPY_TO,
            COPY_FROM,
        ];
        let alias = AAFact::new(1, 2);
        for (key, value) in self.fn_map.iter_mut() {
            if cases.contains(&key.index.as_usize()) {
                value.alias_set.clear();
                value.alias_set.insert(alias.clone());
            }
        }
    }

    fn query_mop(&mut self, def_id: DefId) {
        let fn_name = get_fn_name(self.tcx, def_id);
        rap_trace!("query_mop: {:?}", fn_name);
        /* filter const mir */
        if let Some(_other) = self.tcx.hir_body_const_context(def_id.expect_local()) {
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
