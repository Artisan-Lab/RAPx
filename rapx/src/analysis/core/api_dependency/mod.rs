/// NOTE: This analysis module is currently under development and is highly unstable.
/// The #[allow(unused)] attribute is applied to suppress excessive lint warnings.
/// Once the analysis stabilizes, this marker should be removed.

#[allow(unused)]
pub mod graph;
mod mono;
mod utils;
#[allow(unused)]
mod visitor;

use crate::analysis::Analysis;
pub use graph::ApiDependencyGraph;
pub use graph::{DepEdge, DepNode};
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_middle::ty::TyCtxt;
pub use utils::is_fuzzable_ty;

#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Default)]
pub struct Config {
    pub pub_only: bool,
    pub resolve_generic: bool,
    pub ignore_const_generic: bool,
}

pub fn is_def_id_public(fn_def_id: impl Into<DefId>, tcx: TyCtxt<'_>) -> bool {
    let fn_def_id: DefId = fn_def_id.into();
    let local_id = fn_def_id.expect_local();
    rap_trace!(
        "vis: {:?} (path: {}) => {:?}",
        fn_def_id,
        tcx.def_path_str(fn_def_id),
        tcx.effective_visibilities(()).effective_vis(local_id)
    );
    tcx.effective_visibilities(()).is_directly_public(local_id)
    // || tcx.effective_visibilities(()).is_exported(local_id)
}

pub trait ApiDependencyAnalysis<'tcx> {
    fn get_api_dependency_graph(&self) -> ApiDependencyGraph<'tcx>;
}

pub struct ApiDependencyAnalyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
    config: Config,
    api_graph: ApiDependencyGraph<'tcx>,
}

impl<'tcx> ApiDependencyAnalyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, config: Config) -> ApiDependencyAnalyzer<'tcx> {
        ApiDependencyAnalyzer {
            tcx,
            config,
            api_graph: ApiDependencyGraph::new(tcx),
        }
    }
}

impl<'tcx> Analysis for ApiDependencyAnalyzer<'tcx> {
    fn name(&self) -> &'static str {
        "Default API dependency graph analysis algorithm."
    }

    fn run(&mut self) {
        let local_crate_name = self.tcx.crate_name(LOCAL_CRATE);
        let local_crate_type = self.tcx.crate_types()[0];
        let config = self.config;
        rap_debug!(
            "Build API dependency graph on {} ({}), config = {:?}",
            local_crate_name.as_str(),
            local_crate_type,
            config,
        );

        let mut api_graph = ApiDependencyGraph::new(self.tcx);
        api_graph.build(config);

        let (estimate, total) = api_graph.estimate_coverage();

        let statistics = api_graph.statistics();
        // print all statistics
        rap_info!(
            "API Graph contains {} API nodes, {} type nodes, {} edges",
            statistics.api_count,
            statistics.type_count,
            statistics.edge_cnt
        );
        rap_info!(
            "estimate coverage: {:.2} ({}/{})",
            estimate as f64 / total as f64,
            estimate,
            total
        );
        let dot_path = format!("api_graph_{}_{}.dot", local_crate_name, local_crate_type);
        let json_path = format!("api_graph_{}_{}.json", local_crate_name, local_crate_type);
        rap_info!("Dump API dependency graph to {}", dot_path);
        api_graph.dump_to_dot(dot_path, self.tcx);
        api_graph
            .dump_to_json(&json_path)
            .expect("failed to dump API graph to JSON");
        rap_info!("Dump API dependency graph to {}", json_path);
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
