use crate::{analysis::utils::fn_info::get_cleaned_def_path_name, rap_warn};

use super::{
    contracts::{abstract_state::AlignState, state_lattice::Lattice},
    visitor::BodyVisitor,
};

impl<'tcx> BodyVisitor<'tcx> {
    pub fn check_align(&self, arg: usize) -> bool {
        let obj_ty = self.chains.get_obj_ty_through_chain(arg);
        let var_ty = self.chains.variables.get(&arg);
        if obj_ty.is_none() || var_ty.is_none() {
            rap_warn!(
                "In func {:?}, visitor checker error! Can't get {arg} in chain!",
                get_cleaned_def_path_name(self.tcx, self.def_id)
            );
        }
        let ori_ty = self.visit_ty_and_get_layout(obj_ty.unwrap());
        let cur_ty = self.visit_ty_and_get_layout(var_ty.unwrap().ty);
        return AlignState::Cast(ori_ty, cur_ty).check();
    }
}
