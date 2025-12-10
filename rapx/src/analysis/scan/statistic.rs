use rustc_hir::def_id::DefId;
use std::collections::HashSet;

#[derive(Default)]
pub struct Statistics<'tcx> {
    pub pub_non_generic_api: HashSet<DefId>,
    pub pub_generic_api: HashSet<DefId>,
    pub pub_unsafe_api: HashSet<DefId>,
    pub unsafe_block: Vec<rustc_hir::Block<'tcx>>,
}

pub struct CrateSafetyInfo {
    pub num_total_api: usize,
    pub num_generic_api: usize,
    pub num_unsafe_api: usize,
    pub num_unsafe_block: usize,
}

impl<'tcx> Statistics<'tcx> {
    pub fn total_api_count(&self) -> usize {
        self.pub_non_generic_api.len() + self.pub_generic_api.len()
    }

    pub fn generic_api_count(&self) -> usize {
        self.pub_generic_api.len()
    }

    pub fn num_unsafe_api(&self) -> usize {
        self.pub_unsafe_api.len()
    }

    pub fn num_unsafe_block(&self) -> usize {
        self.unsafe_block.len()
    }

    pub fn info(&self) -> CrateSafetyInfo {
        CrateSafetyInfo {
            num_total_api: self.total_api_count(),
            num_generic_api: self.generic_api_count(),
            num_unsafe_api: self.num_unsafe_api(),
            num_unsafe_block: self.num_unsafe_block(),
        }
    }
}

impl CrateSafetyInfo {
    pub fn print_log(&self) {
        rap_info!("# total api    = {}", self.num_total_api);
        rap_info!("# generic api  = {}", self.num_generic_api);
        rap_info!("# unsafe api   = {}", self.num_unsafe_api);
        rap_info!("# unsafe block = {}", self.num_unsafe_block);
    }
}
