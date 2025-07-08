/// NOTE: This analysis module is currently under development and is highly unstable.
/// The #[allow(unused)] attribute is applied to suppress excessive lint warnings.
/// Once the analysis stabilizes, this marker should be removed.
use crate::{
    analysis::core::api_dependency::{ApiDependencyAnalysis, ApiDependencyGraph},
    rap_debug, rap_info, Analysis,
};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;

use super::visitor::FnVisitor;

pub struct ApiDependencyAnalyzer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub api_graph: ApiDependencyGraph<'tcx>,
}

impl<'tcx> Analysis for ApiDependencyAnalyzer<'tcx> {
    fn name(&self) -> &'static str {
        "Default API dependency graph analysis algorithm."
    }

    fn run(&mut self) {
        self.start();
    }

    fn reset(&mut self) {
        todo!();
    }
}

impl<'tcx> ApiDependencyAnalysis<'tcx> for ApiDependencyAnalyzer<'tcx> {
    fn get_api_dependency_graph(&self) -> ApiDependencyGraph<'tcx> {
        self.api_graph.clone()
    }
}

impl<'tcx> ApiDependencyAnalyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> ApiDependencyAnalyzer<'tcx> {
        ApiDependencyAnalyzer {
            tcx,
            api_graph: ApiDependencyGraph::new(),
        }
    }
    pub fn start(&mut self) {
        let local_crate_name = self.tcx.crate_name(LOCAL_CRATE);
        let local_crate_type = self.tcx.crate_types()[0];
        rap_debug!(
            "Build API dependency graph on {} ({})",
            local_crate_name.as_str(),
            local_crate_type
        );

        let mut api_graph = ApiDependencyGraph::new();
        let mut fn_visitor = FnVisitor::new(self.tcx, &mut api_graph);
        self.tcx.hir_visit_all_item_likes_in_crate(&mut fn_visitor);
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
        self.api_graph = api_graph;
    }
}
