use std::collections::HashSet;

use super::{
    contracts::{abstract_state::AlignState, state_lattice::Lattice},
    matcher::{get_arg_place, UnsafeApi},
    visitor::{BodyVisitor, CheckResult, PlaceTy},
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
            let arg_tuple = get_arg_place(&args[idx].node);
            if arg_tuple.0 == true {
                continue;
            }
            let arg_place = arg_tuple.1;
            let _self_func_name = get_cleaned_def_path_name(self.tcx, self.def_id);
            let func_name = get_cleaned_def_path_name(self.tcx, *def_id);
            for sp in sp_set {
                match sp.sp_name.as_str() {
                    "Aligned" => {
                        if !self.check_align(arg_place) {
                            self.insert_failed_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "Aligned",
                            );
                        } else {
                            self.insert_successful_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "Aligned",
                            );
                        }
                    }
                    "NonNull" => {
                        if !self.check_non_null(arg_place) {
                            self.insert_failed_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "NonNull",
                            );
                        } else {
                            self.insert_successful_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "NonNull",
                            );
                        }
                    }
                    "AllocatorConsistency" => {
                        if !self.check_allocator_consistency(arg_place) {
                            self.insert_failed_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "AllocatorConsistency",
                            );
                        } else {
                            self.insert_successful_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "AllocatorConsistency",
                            );
                        }
                    }
                    "!ZST" => {
                        if !self.check_non_zst(arg_place) {
                            self.insert_failed_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "!ZST",
                            );
                        } else {
                            self.insert_successful_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "!ZST",
                            );
                        }
                    }
                    "Typed" => {
                        if !self.check_typed(arg_place) {
                            self.insert_failed_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "Typed",
                            );
                        } else {
                            self.insert_successful_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "Typed",
                            );
                        }
                    }
                    "Allocated" => {
                        if !self.check_allocated(arg_place) {
                            self.insert_failed_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "Allocated",
                            );
                        } else {
                            self.insert_successful_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "Allocated",
                            );
                        }
                    }
                    "InBounded" => {
                        if !self.check_inbounded(arg_place) {
                            self.insert_failed_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "InBounded",
                            );
                        } else {
                            self.insert_successful_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "InBounded",
                            );
                        }
                    }
                    "ValidString" => {
                        if !self.check_valid_string(arg_place) {
                            self.insert_failed_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "ValidString",
                            );
                        } else {
                            self.insert_successful_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "ValidString",
                            );
                        }
                    }
                    "ValidCStr" => {
                        if !self.check_valid_cstr(arg_place) {
                            self.insert_failed_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "ValidCStr",
                            );
                        } else {
                            self.insert_successful_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "ValidCStr",
                            );
                        }
                    }
                    "ValidInt" => {
                        if !self.check_valid_num(arg_place) {
                            self.insert_failed_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "ValidNum",
                            );
                        } else {
                            self.insert_successful_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "ValidInt",
                            );
                        }
                    }
                    "Init" => {
                        if !self.check_init(arg_place) {
                            self.insert_failed_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "Init",
                            );
                        } else {
                            self.insert_successful_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "Init",
                            );
                        }
                    }
                    "ValidPtr" => {
                        if !self.check_valid_ptr(arg_place) {
                            self.insert_failed_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "ValidPtr",
                            );
                        } else {
                            self.insert_successful_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "ValidPtr",
                            );
                        }
                    }
                    "Ref2Ptr" => {
                        if !self.check_ref_to_ptr(arg_place) {
                            self.insert_failed_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "Ref2Ptr",
                            );
                        } else {
                            self.insert_successful_check_result(
                                func_name.clone(),
                                fn_span,
                                idx + 1,
                                "Ref2Ptr",
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    pub fn insert_failed_check_result(
        &mut self,
        func_name: String,
        fn_span: Span,
        idx: usize,
        sp: &str,
    ) {
        if let Some(existing) = self
            .check_results
            .iter_mut()
            .find(|result| result.func_name == func_name && result.func_span == fn_span)
        {
            if let Some(passed_set) = existing.passed_contracts.get_mut(&idx) {
                passed_set.remove(sp);
                if passed_set.is_empty() {
                    existing.passed_contracts.remove(&idx);
                }
            }
            existing
                .failed_contracts
                .entry(idx)
                .and_modify(|set| {
                    set.insert(sp.to_string());
                })
                .or_insert_with(|| {
                    let mut new_set = HashSet::new();
                    new_set.insert(sp.to_string());
                    new_set
                });
        } else {
            let mut new_result = CheckResult::new(&func_name, fn_span);
            new_result
                .failed_contracts
                .insert(idx, HashSet::from([sp.to_string()]));
            self.check_results.push(new_result);
        }
    }

    pub fn insert_successful_check_result(
        &mut self,
        func_name: String,
        fn_span: Span,
        idx: usize,
        sp: &str,
    ) {
        if let Some(existing) = self
            .check_results
            .iter_mut()
            .find(|result| result.func_name == func_name && result.func_span == fn_span)
        {
            if let Some(failed_set) = existing.failed_contracts.get_mut(&idx) {
                if failed_set.contains(sp) {
                    return;
                }
            }

            existing
                .passed_contracts
                .entry(idx)
                .and_modify(|set| {
                    set.insert(sp.to_string());
                })
                .or_insert_with(|| HashSet::from([sp.to_string()]));
        } else {
            let mut new_result = CheckResult::new(&func_name, fn_span);
            new_result
                .passed_contracts
                .insert(idx, HashSet::from([sp.to_string()]));
            self.check_results.push(new_result);
        }
    }

    // ----------------------Sp checking functions--------------------------

    pub fn check_align(&self, arg: usize) -> bool {
        let obj_ty = self.chains.get_obj_ty_through_chain(arg);
        let var_ty = self.chains.get_var_node(arg);
        if obj_ty.is_none() || var_ty.is_none() {
            rap_warn!(
                "In func {:?}, visitor checker error! Can't get {arg} in chain!",
                get_cleaned_def_path_name(self.tcx, self.def_id)
            );
        }
        let ori_ty = self.visit_ty_and_get_layout(obj_ty.unwrap());
        let cur_ty = self.visit_ty_and_get_layout(var_ty.unwrap().ty.unwrap());
        let point_to_id = self.chains.get_point_to_id(arg);
        let var_ty = self.chains.get_var_node(point_to_id);
        return AlignState::Cast(ori_ty, cur_ty).check() && var_ty.unwrap().states.align;
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
        let point_to_id = self.chains.get_point_to_id(arg);
        let var_ty = self.chains.get_var_node(point_to_id);
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

    pub fn check_valid_num(&self, _arg: usize) -> bool {
        return true;
    }

    pub fn check_init(&self, arg: usize) -> bool {
        let point_to_id = self.chains.get_point_to_id(arg);
        let var_ty = self.chains.get_var_node(point_to_id);
        if var_ty.is_none() {
            rap_warn!(
                "In func {:?}, visitor checker error! Can't get {arg} in chain!",
                get_cleaned_def_path_name(self.tcx, self.def_id)
            );
        }
        return var_ty.unwrap().states.init;
    }

    pub fn check_alias(&self, _arg: usize) -> bool {
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
        return self.check_deref(arg)
            && self.check_init(arg)
            && self.check_align(arg)
            && self.check_alias(arg);
    }
}
