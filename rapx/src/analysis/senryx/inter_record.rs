use std::collections::HashMap;

use super::contracts::abstract_state::AbstractStateItem;

#[derive(Debug, Clone)]
pub struct InterAnalysisRecord<'tcx> {
    pub pre_analysis_state: HashMap<usize, AbstractStateItem<'tcx>>,
    pub post_analysis_state: HashMap<usize, AbstractStateItem<'tcx>>,
    pub ret_state: AbstractStateItem<'tcx>,
}

impl<'tcx> InterAnalysisRecord<'tcx> {
    pub fn new(
        pre_analysis_state: HashMap<usize, AbstractStateItem<'tcx>>,
        post_analysis_state: HashMap<usize, AbstractStateItem<'tcx>>,
        ret_state: AbstractStateItem<'tcx>,
    ) -> Self {
        Self {
            pre_analysis_state,
            post_analysis_state,
            ret_state,
        }
    }

    pub fn is_pre_state_same(
        &self,
        other_pre_state: &HashMap<usize, AbstractStateItem<'tcx>>,
    ) -> bool {
        self.pre_analysis_state == *other_pre_state
    }
}
