pub mod unreserved_hash;
pub mod unreserved_vec;

use unreserved_hash::UnreservedHashCheck;
use unreserved_vec::UnreservedVecCheck;

use crate::analysis::core::dataflow::graph::Graph;
use crate::analysis::opt::OptCheck;

use rustc_middle::ty::TyCtxt;

pub struct ReservationCheck {
    unreserved_hash: UnreservedHashCheck,
    unreserved_vec: UnreservedVecCheck,
}

impl OptCheck for ReservationCheck {
    fn new() -> Self {
        Self {
            unreserved_hash: UnreservedHashCheck::new(),
            unreserved_vec: UnreservedVecCheck::new(),
        }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        self.unreserved_hash.check(graph, tcx);
        self.unreserved_vec.check(graph, tcx);
    }

    fn report(&self, graph: &Graph) {
        self.unreserved_hash.report(graph);
        self.unreserved_vec.report(graph);
    }
}
