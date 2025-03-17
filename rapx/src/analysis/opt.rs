pub mod checking;
pub mod data_collection;
pub mod iterator;
pub mod memory_cloning;

use rustc_middle::ty::TyCtxt;

use crate::rap_warn;

use super::core::dataflow::{graph::Graph, DataFlow};
use checking::bounds_checking::BoundsCheck;
use data_collection::slice_contains::SliceContainsCheck;
use iterator::next_iterator::NextIteratorCheck;
use memory_cloning::used_as_immutable::UsedAsImmutableCheck;

pub struct Opt<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

pub trait OptCheck {
    fn new() -> Self;
    fn check(&mut self, graph: &Graph, tcx: &TyCtxt);
    fn report(&self, graph: &Graph);
}

impl<'tcx> Opt<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    pub fn start(&mut self) {
        let mut dataflow = DataFlow::new(self.tcx, false);
        dataflow.build_graphs();
        let bounds_checks: Vec<BoundsCheck> = dataflow
            .graphs
            .iter()
            .map(|(_, graph)| {
                let mut bounds_check = BoundsCheck::new();
                bounds_check.check(graph, &self.tcx);
                bounds_check
            })
            .collect();
        let used_as_immutable_checks: Vec<UsedAsImmutableCheck> = dataflow
            .graphs
            .iter()
            .map(|(_, graph)| {
                let mut used_as_immutable_check = UsedAsImmutableCheck::new();
                used_as_immutable_check.check(graph, &self.tcx);
                used_as_immutable_check
            })
            .collect();
        let slice_contains_checks: Vec<SliceContainsCheck> = dataflow
            .graphs
            .iter()
            .map(|(_, graph)| {
                let mut slice_contains_check = SliceContainsCheck::new();
                slice_contains_check.check(graph, &self.tcx);
                slice_contains_check
            })
            .collect();
        let next_iterator_checks: Vec<NextIteratorCheck> = dataflow
            .graphs
            .iter()
            .filter_map(|(_, graph)| {
                let mut next_iterator_check = NextIteratorCheck::new();
                next_iterator_check.check(graph, &self.tcx);
                if next_iterator_check.valid {
                    Some(next_iterator_check)
                } else {
                    None
                }
            })
            .collect();
        if !(bounds_checks.is_empty()
            && used_as_immutable_checks.is_empty()
            && slice_contains_checks.is_empty()
            && next_iterator_checks.is_empty())
        {
            rap_warn!("Performance Issues detected");
            for ((_, graph), bounds_check) in dataflow.graphs.iter().zip(bounds_checks.iter()) {
                bounds_check.report(graph);
            }
            for ((_, graph), used_as_immutable_check) in
                dataflow.graphs.iter().zip(used_as_immutable_checks.iter())
            {
                used_as_immutable_check.report(graph);
            }
            for ((_, graph), slice_contains_check) in
                dataflow.graphs.iter().zip(slice_contains_checks.iter())
            {
                slice_contains_check.report(graph);
            }
            for ((_, graph), next_iterator_check) in
                dataflow.graphs.iter().zip(next_iterator_checks.iter())
            {
                next_iterator_check.report(graph);
            }
        }
    }
}
