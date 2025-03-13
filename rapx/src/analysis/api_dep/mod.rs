mod extract;
mod graph;
mod lifetime;
mod visitor;
use crate::{rap_debug, rap_info};
use graph::ApiDepGraph;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;

use visitor::FnVisitor;

pub struct ApiDep<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> ApiDep<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> ApiDep<'tcx> {
        ApiDep { tcx }
    }
    pub fn start(&self) -> ApiDepGraph<'tcx> {
        let local_crate_name = self.tcx.crate_name(LOCAL_CRATE);
        let local_crate_type = self.tcx.crate_types()[0];
        rap_debug!(
            "Build API dependency graph on {} ({})",
            local_crate_name.as_str(),
            local_crate_type
        );

        let mut api_graph = ApiDepGraph::new();
        let mut fn_visitor = FnVisitor::new(self.tcx, &mut api_graph);
        self.tcx
            .hir()
            .visit_all_item_likes_in_crate(&mut fn_visitor);
        rap_debug!("api-dep find {} APIs.", fn_visitor.fn_cnt());

        let statistics = api_graph.statistics();
        // print all statistics
        rap_debug!(
            "API Graph contains {} API nodes, {} type nodes, {} generic parameter def nodes",
            statistics.api_count,
            statistics.type_count,
            statistics.generic_param_count
        );

        let dot_filename = format!("api_graph_{}_{}.dot", local_crate_name, local_crate_type);
        rap_info!("Dump API dependency graph to {}", dot_filename);
        api_graph.dump_to_dot(dot_filename, self.tcx);
        api_graph
    }
}
