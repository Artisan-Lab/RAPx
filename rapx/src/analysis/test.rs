use crate::{
    analysis::{
        core::{
            alias_analysis::{default::AliasAnalyzer, AAResultMapWrapper, AliasAnalysis},
            dataflow::{default::DataFlowAnalyzer, DataFlowAnalysis, DataFlowGraphMapWrapper},
            ownedheap_analysis::{default::OwnedHeapAnalyzer, OHAResultMapWrapper, OwnedHeapAnalysis},
            range_analysis::{default::RangeAnalyzer, PathConstraintMapWrapper, RangeAnalysis},
        },
        Analysis,
    },
    rap_info,
};

use rustc_middle::ty::TyCtxt;

pub struct Test<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> Test<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    pub fn start(&self) {
        let mut alias_analysis = AliasAnalyzer::new(self.tcx);
        alias_analysis.run();
        let result = alias_analysis.get_local_fn_alias();
        rap_info!("{}", AAResultMapWrapper(result));

        let mut dataflow_analysis = DataFlowAnalyzer::new(self.tcx, false);
        dataflow_analysis.run();
        let dataflow_graph = dataflow_analysis.get_all_dataflow();
        rap_info!("{}", DataFlowGraphMapWrapper(dataflow_graph));

        let mut heap_analysis = OwnedHeapAnalyzer::new(self.tcx);
        heap_analysis.run();
        let result = heap_analysis.get_all_items();
        rap_info!("{}", OHAResultMapWrapper(result));

        let mut range_analysis = RangeAnalyzer::<i128>::new(self.tcx, false);
        range_analysis.run();
        let path_constraint = range_analysis.get_all_path_constraints();
        rap_info!("{}", PathConstraintMapWrapper(path_constraint));
    }
}
