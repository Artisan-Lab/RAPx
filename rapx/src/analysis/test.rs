use crate::{
    analysis::{
        core::{
            alias_analysis::{default::AliasAnalyzer, AAResultMapWrapper, AliasAnalysis},
            ownedheap_analysis::default::OwnedHeapAnalyzer,
            range_analysis::default::RangeAnalyzer,
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

        let mut heap_analysis = OwnedHeapAnalyzer::new(self.tcx);
        heap_analysis.run();

        let mut range_analysis = RangeAnalyzer::<i128>::new(self.tcx, false);
        range_analysis.run();
    }
}
