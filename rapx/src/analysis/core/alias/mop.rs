pub mod alias;
pub mod graph;
pub mod mop;
pub mod types;

use crate::analysis::core::alias::AAFact;
use crate::analysis::core::alias::{AAResult, AliasAnalysis};
use crate::analysis::utils::intrinsic_id::{
    COPY_FROM, COPY_FROM_NONOVERLAPPING, COPY_TO, COPY_TO_NONOVERLAPPING,
};
use crate::analysis::Analysis;
use crate::utils::source::*;
use crate::{rap_debug, rap_info, rap_trace};
use graph::MopGraph;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::collections::HashSet;
use std::fmt;

pub const VISIT_LIMIT: usize = 1000;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct MopAAFact {
    pub fact: AAFact,
    pub lhs_may_drop: bool,
    pub lhs_need_drop: bool,
    pub rhs_may_drop: bool,
    pub rhs_need_drop: bool,
}

impl MopAAFact {
    pub fn new(
        lhs_no: usize,
        lhs_may_drop: bool,
        lhs_need_drop: bool,
        rhs_no: usize,
        rhs_may_drop: bool,
        rhs_need_drop: bool,
    ) -> MopAAFact {
        MopAAFact {
            fact: AAFact::new(lhs_no, rhs_no),
            lhs_may_drop,
            lhs_need_drop,
            rhs_may_drop,
            rhs_need_drop,
        }
    }

    pub fn valuable(&self) -> bool {
        return self.lhs_may_drop && self.rhs_may_drop;
    }

    pub fn swap(&mut self) {
        self.fact.swap();
        std::mem::swap(&mut self.lhs_may_drop, &mut self.rhs_may_drop);
        std::mem::swap(&mut self.lhs_need_drop, &mut self.rhs_need_drop);
    }

    pub fn lhs_no(&self) -> usize {
        self.fact.lhs_no
    }

    pub fn rhs_no(&self) -> usize {
        self.fact.rhs_no
    }

    pub fn lhs_fields(&self) -> &[usize] {
        &self.fact.lhs_fields
    }

    pub fn rhs_fields(&self) -> &[usize] {
        &self.fact.rhs_fields
    }
}

#[derive(Debug, Clone)]
pub struct MopAAResult {
    arg_size: usize,
    alias_set: HashSet<MopAAFact>,
}


impl fmt::Display for MopAAResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{{{}}}",
            self.aliases()
                .iter()
                .map(|alias| format!("{}", alias.fact))
                .collect::<Vec<String>>()
                .join(",")
        )
    }
}

impl MopAAResult {
    pub fn new(arg_size: usize) -> MopAAResult {
        Self {
            arg_size,
            alias_set: HashSet::new(),
        }
    }

    pub fn arg_size(&self) -> usize {
        self.arg_size
    }

    pub fn aliases(&self) -> &HashSet<MopAAFact> {
        &self.alias_set
    }

    pub fn add_alias(&mut self, alias: MopAAFact) {
        self.alias_set.insert(alias);
    }

    pub fn len(&self) -> usize {
        self.alias_set.len()
    }

    pub fn sort_alias_index(&mut self) {
        let alias_set = std::mem::take(&mut self.alias_set);
        let mut new_alias_set = HashSet::with_capacity(alias_set.len());

        for mut ra in alias_set.into_iter() {
            if ra.lhs_no() >= ra.rhs_no() {
                ra.swap();
            }
            new_alias_set.insert(ra);
        }
        self.alias_set = new_alias_set;
    }
}

impl Into<AAResult> for MopAAResult {
    fn into(self) -> AAResult {
        AAResult {
            arg_size: self.arg_size,
            alias_set: self.alias_set.into_iter().map(|alias| alias.fact).collect(),
        }
    }
}

//struct to cache the results for analyzed functions.
pub type FnMap = FxHashMap<DefId, MopAAResult>;

pub struct MopAlias<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub fn_map: FnMap,
}

impl<'tcx> Analysis<DefId, AAResult> for MopAlias<'tcx> {
    fn name(&self) -> &'static str {
        "Alias Analysis (MoP)"
    }

    fn get(&mut self, query: DefId) -> AAResult {
        self.fn_map
            .get(&query)
            .expect(&format!("cannot find alias analysis result for {query:?}"))
            .clone()
            .into()
    }
}

impl<'tcx> AliasAnalysis for MopAlias<'tcx> {}

impl<'tcx> MopAlias<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            fn_map: FxHashMap::default(),
        }
    }

    pub fn start(&mut self) -> &FnMap {
        rap_debug!("Start alias analysis via MoP.");
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
        &self.fn_map
    }

    pub fn handle_conor_cases(&mut self) {
        let cases = [
            COPY_FROM_NONOVERLAPPING,
            COPY_TO_NONOVERLAPPING,
            COPY_TO,
            COPY_FROM,
        ];
        let alias = MopAAFact::new(1, true, true, 2, true, true);
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
