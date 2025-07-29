use std::collections::HashSet;

use super::{
    contracts::{abstract_state::AlignState, state_lattice::Lattice},
    matcher::{get_arg_place, UnsafeApi},
    visitor::{BodyVisitor, CheckResult, PlaceTy},
};
use crate::{
    analysis::{
        core::{
            alias_analysis::AAResult,
            dataflow::{default::DataFlowAnalyzer, DataFlowAnalysis},
        },
        senryx::contracts::property::{CisRange, CisRangeItem, PropertyContract},
        utils::fn_info::{
            display_hashmap, generate_contract_from_annotation_without_field_types,
            get_cleaned_def_path_name, is_strict_ty_convert, reflect_generic,
        },
    },
    rap_debug, rap_error, rap_info, rap_warn,
};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::BinOp;
use rustc_middle::mir::Operand;
use rustc_middle::mir::Place;
use rustc_middle::ty::Ty;
use rustc_span::source_map::Spanned;
use rustc_span::Span;

impl<'tcx> BodyVisitor<'tcx> {
    pub fn handle_std_unsafe_call(
        &mut self,
        _dst_place: &Place<'_>,
        def_id: &DefId,
        args: &[Spanned<Operand>],
        _path_index: usize,
        _fn_map: &FxHashMap<DefId, AAResult>,
        fn_span: Span,
        fn_result: UnsafeApi,
        generic_mapping: FxHashMap<String, Ty<'tcx>>,
    ) {
        let func_name = get_cleaned_def_path_name(self.tcx, *def_id);
        let args_with_contracts =
            generate_contract_from_annotation_without_field_types(self.tcx, *def_id);
        rap_debug!(
            "Checking contracts {:?} for {:?}",
            args_with_contracts,
            def_id
        );
        let mut count = 0;
        for (base, fields, contract) in args_with_contracts {
            rap_debug!("Find contract for {:?}, {base}: {:?}", def_id, contract);
            if base == 0 {
                rap_warn!("Wrong base index for {:?}, with {:?}", def_id, contract);
                continue;
            }
            let arg_tuple = get_arg_place(&args[base - 1].node);
            // if this arg is a constant
            if arg_tuple.0 {
                continue; //TODO: check the constant value
            } else {
                let arg_place = self.chains.find_var_id_with_fields_seq(arg_tuple.1, fields);
                self.check_contract(
                    arg_place,
                    args,
                    contract,
                    &generic_mapping,
                    func_name.clone(),
                    fn_span,
                    count,
                );
            }
            count += 1;
        }

        for (idx, sp_set) in fn_result.sps.iter().enumerate() {
            if args.is_empty() {
                break;
            }
            let arg_tuple = get_arg_place(&args[idx].node);
            // if this arg is a constant
            if arg_tuple.0 {
                continue;
            }
            let arg_place = arg_tuple.1;
            let _self_func_name = get_cleaned_def_path_name(self.tcx, self.def_id);
            let func_name = get_cleaned_def_path_name(self.tcx, *def_id);
            for sp in sp_set {
                match sp.sp_name.as_str() {
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
                        if !self.check_allocator_consistency(func_name.clone(), arg_place) {
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

    pub fn insert_checking_result(
        &mut self,
        sp: &str,
        is_passed: bool,
        func_name: String,
        fn_span: Span,
        idx: usize,
    ) {
        if is_passed {
            self.insert_successful_check_result(func_name.clone(), fn_span, idx + 1, sp);
        } else {
            self.insert_failed_check_result(func_name.clone(), fn_span, idx + 1, sp);
        }
    }

    pub fn check_contract(
        &mut self,
        arg: usize,
        args: &[Spanned<Operand>],
        contract: PropertyContract<'tcx>,
        generic_mapping: &FxHashMap<String, Ty<'tcx>>,
        func_name: String,
        fn_span: Span,
        idx: usize,
    ) -> bool {
        match contract {
            PropertyContract::Align(ty) => {
                let contract_required_ty = reflect_generic(generic_mapping, ty);
                rap_debug!(
                    "peel generic ty for {:?}, actual_ty is {:?}",
                    func_name.clone(),
                    contract_required_ty
                );
                if !self.check_align(arg, contract_required_ty) {
                    self.insert_checking_result("Align", false, func_name, fn_span, idx);
                } else {
                    rap_debug!("Checking Align passed for {func_name} in {:?}!", fn_span);
                    self.insert_checking_result("Align", true, func_name, fn_span, idx);
                }
            }
            PropertyContract::InBound(ty, contract_len) => {
                let contract_ty = reflect_generic(generic_mapping, ty);
                if let CisRangeItem::Var(base, len_fields) = contract_len {
                    let base_tuple = get_arg_place(&args[base - 1].node);
                    let length_arg = self
                        .chains
                        .find_var_id_with_fields_seq(base_tuple.1, len_fields);
                    if !self.check_inbound(arg, length_arg, contract_ty) {
                        self.insert_checking_result("InBound", false, func_name, fn_span, idx);
                    } else {
                        rap_info!("Checking InBound passed for {func_name} in {:?}!", fn_span);
                        self.insert_checking_result("InBound", true, func_name, fn_span, idx);
                    }
                } else {
                    rap_error!("Wrong arg {:?} in Inbound safety check!", contract_len);
                }
            }
            PropertyContract::NonNull => {
                self.check_non_null(arg);
            }
            _ => {}
        }
        true
    }

    // ----------------------Sp checking functions--------------------------

    // TODO: Currently can not support unaligned offset checking
    pub fn check_align(&self, arg: usize, contract_required_ty: Ty<'tcx>) -> bool {
        // rap_warn!("Checking Align {arg}!");
        // display_hashmap(&self.chains.variables, 1);
        // 1. Check the var's cis.
        let var = self.chains.get_var_node(arg).unwrap();
        let required_ty = self.visit_ty_and_get_layout(contract_required_ty);
        for cis in &var.cis.contracts {
            if let PropertyContract::Align(cis_ty) = cis {
                let ori_ty = self.visit_ty_and_get_layout(*cis_ty);
                return AlignState::Cast(ori_ty, required_ty).check();
            }
        }
        // 2. If the var does not have cis, then check its type and the value type
        let mem = self.chains.get_obj_ty_through_chain(arg);
        let mem_ty = self.visit_ty_and_get_layout(mem.unwrap());
        let cur_ty = self.visit_ty_and_get_layout(var.ty.unwrap());
        let point_to_id = self.chains.get_point_to_id(arg);
        let var_ty = self.chains.get_var_node(point_to_id);
        // display_hashmap(&self.chains.variables, 1);
        // rap_warn!("{:?}, {:?}, {:?}, {:?}", arg, cur_ty, point_to_id, mem_ty);
        return AlignState::Cast(mem_ty, cur_ty).check() && var_ty.unwrap().ots.align;
    }

    pub fn check_non_zst(&self, arg: usize) -> bool {
        let obj_ty = self.chains.get_obj_ty_through_chain(arg);
        if obj_ty.is_none() {
            self.show_error_info(arg);
        }
        let ori_ty = self.visit_ty_and_get_layout(obj_ty.unwrap());
        match ori_ty {
            PlaceTy::Ty(_align, size) => size == 0,
            PlaceTy::GenericTy(_, _, tys) => {
                if tys.is_empty() {
                    return false;
                }
                for (_, size) in tys {
                    if size != 0 {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }

    // checking the value ptr points to is valid for its type
    pub fn check_typed(&self, arg: usize) -> bool {
        let obj_ty = self.chains.get_obj_ty_through_chain(arg).unwrap();
        let var = self.chains.get_var_node(arg);
        // display_hashmap(&self.chains.variables, 1);
        let var_ty = var.unwrap().ty.unwrap();
        if obj_ty != var_ty && is_strict_ty_convert(self.tcx, obj_ty, var_ty) {
            return false;
        }
        self.check_init(arg)
    }

    pub fn check_non_null(&self, arg: usize) -> bool {
        let point_to_id = self.chains.get_point_to_id(arg);
        let var_ty = self.chains.get_var_node(point_to_id);
        if var_ty.is_none() {
            self.show_error_info(arg);
        }
        var_ty.unwrap().ots.nonnull
    }

    // check each field's init state in the tree.
    // check arg itself when it doesn't have fields.
    pub fn check_init(&self, arg: usize) -> bool {
        let point_to_id = self.chains.get_point_to_id(arg);
        let var = self.chains.get_var_node(point_to_id);
        // display_hashmap(&self.chains.variables, 1);
        if var.unwrap().field.is_empty() {
            let mut init_flag = true;
            for field in &var.unwrap().field {
                init_flag &= self.check_init(*field.1);
            }
            init_flag
        } else {
            var.unwrap().ots.init
        }
    }

    pub fn check_allocator_consistency(&self, _func_name: String, _arg: usize) -> bool {
        true
    }

    pub fn check_allocated(&self, _arg: usize) -> bool {
        true
    }

    pub fn check_inbound(&self, arg: usize, length_arg: usize, contract_ty: Ty<'tcx>) -> bool {
        // 1. Check the var's cis.
        let mem_arg = self.chains.get_point_to_id(arg);
        let mem_var = self.chains.get_var_node(mem_arg).unwrap();
        for cis in &mem_var.cis.contracts {
            if let PropertyContract::InBound(cis_ty, len) = cis {
                // display_hashmap(&self.chains.variables, 1);
                return self.check_le_op(&contract_ty, length_arg, cis_ty, len);
            }
        }
        false
    }

    /// return the result of less equal comparison （left_len * left_ty <= right_len * right_ty）
    fn check_le_op(
        &self,
        left_ty: &Ty<'tcx>,
        left_arg: usize,
        right_ty: &Ty<'tcx>,
        right_len: &CisRangeItem,
    ) -> bool {
        // If they have same types, then compare the length
        // rap_warn!("{:?}, {left_arg}, {:?}, {:?}", left_ty, right_ty, right_len);
        // If they have the same type, compare their patial order
        if left_ty == right_ty {
            return self
                .compare_patial_order_of_two_args(left_arg, right_len.get_var_base().unwrap());
        }
        // Otherwise, take size of types into consideration
        let left_layout = self.visit_ty_and_get_layout(*left_ty);
        let right_layout = self.visit_ty_and_get_layout(*right_ty);
        let get_size_range = |layout: &PlaceTy<'tcx>| -> Option<(u128, u128)> {
            match layout {
                PlaceTy::Ty(_, size) => Some((*size as u128, *size as u128)),
                PlaceTy::GenericTy(_, _, layouts) if !layouts.is_empty() => {
                    let sizes: Vec<u128> = layouts.iter().map(|(_, s)| *s as u128).collect();
                    let min = *sizes.iter().min().unwrap();
                    let max = *sizes.iter().max().unwrap();
                    Some((min, max))
                }
                _ => None,
            }
        };
        let (left_min_size, left_max_size) = match get_size_range(&left_layout) {
            Some(range) => range,
            None => return false, // Can not detemine size
        };
        let (right_min_size, right_max_size) = match get_size_range(&right_layout) {
            Some(range) => range,
            None => return false, // Can not detemine size
        };
        // TODO:

        false
    }

    /// compare two args, return true if left <= right
    fn compare_patial_order_of_two_args(&self, left: usize, right: usize) -> bool {
        // Find the same value node set
        let mut dataflow_analyzer = DataFlowAnalyzer::new(self.tcx, false);
        dataflow_analyzer.build_graph(self.def_id);
        let left_local = rustc_middle::mir::Local::from(left);
        let right_local = rustc_middle::mir::Local::from(right);
        let left_local_set = dataflow_analyzer.collect_equivalent_locals(self.def_id, left_local);
        let right_local_set = dataflow_analyzer.collect_equivalent_locals(self.def_id, right_local);
        // If left == right
        if right_local_set.contains(&rustc_middle::mir::Local::from(left)) {
            return true;
        }
        // rap_warn!(
        //     "left_local: {:?}, left set: {:?}, right_local:{:?}, right set: {:?}",
        //     left_local,
        //     left_local_set,
        //     right_local,
        //     right_local_set
        // );
        for left_local_item in left_local_set {
            let left_var = self.chains.get_var_node(left_local_item.as_usize());
            if left_var.is_none() {
                continue;
            }
            for cis in &left_var.unwrap().cis.contracts {
                if let PropertyContract::ValidNum(cis_range) = cis {
                    let cis_len = &cis_range.range;
                    match cis_range.bin_op {
                        BinOp::Le | BinOp::Lt | BinOp::Eq => {
                            return cis_len.get_var_base().is_some()
                                && right_local_set.contains(&rustc_middle::mir::Local::from(
                                    cis_len.get_var_base().unwrap(),
                                ));
                        }
                        _ => {}
                    }
                }
            }
        }
        false
    }

    // fn compare_cis_range(&self, cis_range: CisRange, right_len: &CisRangeItem) -> bool {
    //     false
    // }

    pub fn check_valid_string(&self, _arg: usize) -> bool {
        true
    }

    pub fn check_valid_cstr(&self, _arg: usize) -> bool {
        true
    }

    pub fn check_valid_num(&self, _arg: usize) -> bool {
        true
    }

    pub fn check_alias(&self, _arg: usize) -> bool {
        true
    }

    // Compound SPs
    pub fn check_valid_ptr(&self, arg: usize) -> bool {
        !self.check_non_zst(arg) || (self.check_non_zst(arg) && self.check_deref(arg))
    }

    pub fn check_deref(&self, arg: usize) -> bool {
        self.check_allocated(arg)
        // && self.check_inbounded(arg)
    }

    pub fn check_ref_to_ptr(&self, arg: usize) -> bool {
        self.check_deref(arg)
            && self.check_init(arg)
            // && self.check_align(arg)
            && self.check_alias(arg)
    }

    pub fn show_error_info(&self, arg: usize) {
        rap_warn!(
            "In func {:?}, visitor checker error! Can't get {arg} in chain!",
            get_cleaned_def_path_name(self.tcx, self.def_id)
        );
        display_hashmap(&self.chains.variables, 1);
    }
}
