use super::{
    contracts::{abstract_state::AlignState, state_lattice::Lattice},
    matcher::{get_arg_place, UnsafeApi},
    visitor::{BodyVisitor, PlaceTy},
};
use crate::analysis::senryx::FnMap;
use crate::{analysis::utils::fn_info::get_cleaned_def_path_name, rap_warn};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Operand;
use rustc_middle::mir::Place;
use rustc_span::source_map::Spanned;
use rustc_span::Span;

impl<'tcx> BodyVisitor<'tcx> {
    pub fn handle_std_unsafe_call(
        &mut self,
        _dst_place: &Place<'_>,
        def_id: &DefId,
        args: &Box<[Spanned<Operand>]>,
        _path_index: usize,
        _fn_map: &FnMap,
        fn_span: Span,
        fn_result: UnsafeApi,
    ) {
        for (idx, sp_set) in fn_result.sps.iter().enumerate() {
            if args.len() == 0 {
                break;
            }
            let arg_place = get_arg_place(&args[idx].node);
            if arg_place == 0 {
                continue;
            }
            let self_func_name = get_cleaned_def_path_name(self.tcx, self.def_id);
            let func_name = get_cleaned_def_path_name(self.tcx, *def_id);
            for sp in sp_set {
                match sp.sp_name.as_str() {
                    "Aligned" => {
                        if !self.check_align(arg_place) {
                            rap_warn!("Safe function {:?} uses unsafe callee {:?}, but the pointer may be unaligned!",self_func_name, func_name);
                            rap_warn!("{:?}", fn_span);
                        }
                    }
                    "NonNull" => {
                        if !self.check_non_null(arg_place) {
                            rap_warn!("Safe function {:?} uses unsafe callee {:?}, but the pointer may be null!",self_func_name, func_name);
                            rap_warn!("{:?}", fn_span);
                        }
                    }
                    "AllocatorConsistency" => {
                        if !self.check_allocator_consistency(arg_place) {
                            rap_warn!("Safe function {:?} uses unsafe callee {:?}, but allocator may be inconsistency!",self_func_name, func_name);
                            rap_warn!("{:?}", fn_span);
                        }
                    }
                    "!ZST" => {
                        if !self.check_non_zst(arg_place) {
                            rap_warn!("Safe function {:?} uses unsafe callee {:?}, but the argument may be ZST!",self_func_name, func_name);
                            rap_warn!("{:?}", fn_span);
                        }
                    }
                    "Typed" => {
                        if !self.check_typed(arg_place) {
                            rap_warn!("Safe function {:?} uses unsafe callee {:?}, but the argument may not be typed!",self_func_name, func_name);
                            rap_warn!("{:?}", fn_span);
                        }
                    }
                    "Allocated" => {
                        if !self.check_allocated(arg_place) {
                            rap_warn!("Safe function {:?} uses unsafe callee {:?}, but the memory access may be out of range!",self_func_name, func_name);
                            rap_warn!("{:?}", fn_span);
                        }
                    }
                    "InBounded" => {
                        if !self.check_inbounded(arg_place) {
                            rap_warn!("Safe function {:?} uses unsafe callee {:?}, but the access may be out of range!",self_func_name, func_name);
                            rap_warn!("{:?}", fn_span);
                        }
                    }
                    "ValidString" => {
                        if !self.check_valid_string(arg_place) {
                            rap_warn!("Safe function {:?} uses unsafe callee {:?}, but the input may be invalid!",self_func_name, func_name);
                            rap_warn!("{:?}", fn_span);
                        }
                    }
                    "ValidCStr" => {
                        if !self.check_valid_cstr(arg_place) {
                            rap_warn!("Safe function {:?} uses unsafe callee {:?}, but the input may be invalid!",self_func_name, func_name);
                            rap_warn!("{:?}", fn_span);
                        }
                    }
                    "ValidInt" => {
                        if !self.check_valid_int(arg_place) {
                            rap_warn!("Safe function {:?} uses unsafe callee {:?}, but the input may be invalid!",self_func_name, func_name);
                            rap_warn!("{:?}", fn_span);
                        }
                    }
                    "Init" => {
                        if !self.check_init(arg_place) {
                            rap_warn!("Safe function {:?} uses unsafe callee {:?}, but the memory may be uninitialized!",self_func_name, func_name);
                            rap_warn!("{:?}", fn_span);
                        }
                    }
                    "ValidPtr" => {
                        if !self.check_valid_ptr(arg_place) {
                            rap_warn!("Safe function {:?} uses unsafe callee {:?}, but the ptr may be invalid!",self_func_name, func_name);
                            rap_warn!("{:?}", fn_span);
                        }
                    }
                    "Ref2Ptr" => {
                        if !self.check_ref_to_ptr(arg_place) {
                            rap_warn!("Safe function {:?} uses unsafe callee {:?}, but the ref may be invalid!",self_func_name, func_name);
                            rap_warn!("{:?}", fn_span);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

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
        let cur_ty = self.visit_ty_and_get_layout(var_ty.unwrap().ty.unwrap());
        return AlignState::Cast(ori_ty, cur_ty).check();
    }

    pub fn check_non_zst(&self, arg: usize) -> bool {
        let obj_ty = self.chains.get_obj_ty_through_chain(arg);
        if obj_ty.is_none() {
            rap_warn!(
                "In func {:?}, visitor checker error! Can't get {arg} in chain!",
                get_cleaned_def_path_name(self.tcx, self.def_id)
            );
        }
        let ori_ty = self.visit_ty_and_get_layout(obj_ty.unwrap());
        match ori_ty {
            PlaceTy::Ty(_align, size) => {
                return size == 0;
            }
            PlaceTy::GenericTy(_, _, tys) => {
                if tys.len() == 0 {
                    return false;
                }
                for (_, size) in tys {
                    if size != 0 {
                        return false;
                    }
                }
                return true;
            }
            _ => return false,
        }
    }

    pub fn check_typed(&self, _arg: usize) -> bool {
        return true;
    }

    pub fn check_non_null(&self, arg: usize) -> bool {
        let var_ty = self.chains.variables.get(&arg);
        if var_ty.is_none() {
            rap_warn!(
                "In func {:?}, visitor checker error! Can't get {arg} in chain!",
                get_cleaned_def_path_name(self.tcx, self.def_id)
            );
        }
        return var_ty.unwrap().states.nonnull;
    }

    pub fn check_allocator_consistency(&self, _arg: usize) -> bool {
        return true;
    }

    pub fn check_allocated(&self, _arg: usize) -> bool {
        return true;
    }

    pub fn check_inbounded(&self, _arg: usize) -> bool {
        return true;
    }

    pub fn check_valid_string(&self, _arg: usize) -> bool {
        return true;
    }

    pub fn check_valid_cstr(&self, _arg: usize) -> bool {
        return true;
    }

    pub fn check_valid_int(&self, _arg: usize) -> bool {
        return true;
    }

    pub fn check_init(&self, _arg: usize) -> bool {
        return true;
    }

    // Compound SPs
    pub fn check_valid_ptr(&self, arg: usize) -> bool {
        return !self.check_non_zst(arg) || (self.check_non_zst(arg) && self.check_deref(arg));
    }

    pub fn check_deref(&self, arg: usize) -> bool {
        return self.check_allocated(arg) && self.check_inbounded(arg);
    }

    pub fn check_ref_to_ptr(&self, arg: usize) -> bool {
        return self.check_allocated(arg)
            && self.check_inbounded(arg)
            && self.check_init(arg)
            && self.check_align(arg);
    }
}
