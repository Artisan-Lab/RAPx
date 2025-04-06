pub mod checking;
pub mod data_collection;
pub mod iterator;
pub mod memory_cloning;

use rustc_middle::ty::TyCtxt;

use super::core::dataflow::{graph::Graph, DataFlow};
use checking::bounds_checking::BoundsCheck;
use data_collection::slice_contains::SliceContainsCheck;
use data_collection::unreserved_hash::UnreservedHashCheck;
use iterator::next_iterator::NextIteratorCheck;
use memory_cloning::hash_key_cloning::HashKeyCloningCheck;

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
        dataflow.graphs.iter().for_each(|(_, graph)| {
            let mut bounds_check = BoundsCheck::new();
            bounds_check.check(graph, &self.tcx);
            bounds_check.report(graph);

            let mut hash_key_cloning_check = HashKeyCloningCheck::new();
            hash_key_cloning_check.check(graph, &self.tcx);
            hash_key_cloning_check.report(graph);

            let mut slice_contains_check = SliceContainsCheck::new();
            slice_contains_check.check(graph, &self.tcx);
            slice_contains_check.report(graph);

            let mut next_iterator_check = NextIteratorCheck::new();
            next_iterator_check.check(graph, &self.tcx);
            if next_iterator_check.valid {
                next_iterator_check.report(graph);
            }

            let mut unreserved_hash_check = UnreservedHashCheck::new();
            unreserved_hash_check.check(graph, &self.tcx);
            unreserved_hash_check.report(graph);
        });
    }
}
