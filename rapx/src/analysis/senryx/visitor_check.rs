use std::collections::HashSet;

use super::{
    contracts::{abstract_state::AlignState, state_lattice::Lattice},
    matcher::{UnsafeApi, get_arg_place},
    visitor::{BodyVisitor, CheckResult, PlaceTy},
};
use crate::{
    analysis::{
        core::{
            alias_analysis::AAResult,
            dataflow::{DataFlowAnalysis, default::DataFlowAnalyzer},
        },
        senryx::contracts::property::{CisRange, CisRangeItem, PropertyContract},
        utils::fn_info::{
            display_hashmap, generate_contract_from_annotation_without_field_types,
            generate_contract_from_std_annotation_json, get_cleaned_def_path_name,
            is_strict_ty_convert, reflect_generic,
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
use rustc_span::Span;
use rustc_span::source_map::Spanned;

impl<'tcx> BodyVisitor<'tcx> {
    /// Entry point for handling standard library unsafe API calls and verifying their contracts.
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

        // If the target API has contract annotation in signature,
        // this fn-call could be replaced with 'generate_contract_from_annotation_without_field_types(self.tcx, *def_id);'
        let args_with_contracts = generate_contract_from_std_annotation_json(self.tcx, *def_id);

        for (idx, (base, fields, contract)) in args_with_contracts.iter().enumerate() {
            rap_debug!("Find contract for {:?}, {base}: {:?}", def_id, contract);
            let arg_tuple = get_arg_place(&args[*base].node);
            // if this arg is a constant
            if arg_tuple.0 {
                continue; //TODO: check the constant value
            } else {
                let arg_place = self.chains.find_var_id_with_fields_seq(arg_tuple.1, fields);
                self.check_contract(
                    arg_place,
                    args,
                    contract.clone(),
                    &generic_mapping,
                    func_name.clone(),
                    fn_span,
                    idx,
                );
            }
        }
    }

    /// Dispatcher function that validates a specific contract type.
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
        let (sp_name, check_result) = match contract {
            PropertyContract::Align(ty) => {
                let contract_required_ty = reflect_generic(generic_mapping, &func_name, ty);
                let check_result = self.check_align(arg, contract_required_ty);
                ("Align", check_result)
            }
            PropertyContract::InBound(ty, contract_len) => {
                let contract_required_ty = reflect_generic(generic_mapping, &func_name, ty);
                let check_result = self.check_inbound(arg, contract_len, contract_required_ty);
                ("Inbound", check_result)
            }
            PropertyContract::NonNull => {
                let check_result = self.check_non_null(arg);
                ("NonNull", check_result)
            }
            PropertyContract::Typed(ty) => {
                let check_result = self.check_typed(arg);
                ("Typed", check_result)
            }
            PropertyContract::ValidPtr(ty, contract_len) => {
                let contract_required_ty = reflect_generic(generic_mapping, &func_name, ty);
                let check_result = self.check_valid_ptr(arg, contract_len, contract_required_ty);
                ("ValidPtr", check_result)
            }
            _ => ("Unknown", false),
        };

        self.insert_checking_result(sp_name, check_result, func_name, fn_span, idx);
        true
    }

    // ---------------------- Sp checking functions --------------------------

    // TODO: Currently can not support unaligned offset checking
    pub fn check_align(&self, arg: usize, contract_required_ty: Ty<'tcx>) -> bool {
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

    pub fn check_inbound(
        &self,
        arg: usize,
        length_arg: CisRangeItem,
        contract_ty: Ty<'tcx>,
    ) -> bool {
        false
    }

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

    // --------------------- Checking Compound SPs ---------------------

    pub fn check_valid_ptr(
        &self,
        arg: usize,
        length_arg: CisRangeItem,
        contract_ty: Ty<'tcx>,
    ) -> bool {
        !self.check_non_zst(arg)
            || (self.check_non_zst(arg) && self.check_deref(arg, length_arg, contract_ty))
    }

    pub fn check_deref(&self, arg: usize, length_arg: CisRangeItem, contract_ty: Ty<'tcx>) -> bool {
        self.check_allocated(arg) && self.check_inbound(arg, length_arg, contract_ty)
    }

    pub fn check_ref_to_ptr(
        &self,
        arg: usize,
        length_arg: CisRangeItem,
        contract_ty: Ty<'tcx>,
    ) -> bool {
        self.check_deref(arg, length_arg, contract_ty)
            && self.check_init(arg)
            && self.check_align(arg, contract_ty)
            && self.check_alias(arg)
    }

    // -------------------------- helper functions: insert checking results --------------------------

    // Insert result general API
    pub fn insert_checking_result(
        &mut self,
        sp: &str,
        is_passed: bool,
        func_name: String,
        fn_span: Span,
        idx: usize,
    ) {
        if sp == "Unknown" {
            return;
        }
        if is_passed {
            self.insert_successful_check_result(func_name.clone(), fn_span, idx + 1, sp);
        } else {
            self.insert_failed_check_result(func_name.clone(), fn_span, idx + 1, sp);
        }
    }

    // Insert falied SP result
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

    // Insert successful SP result
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

    pub fn show_error_info(&self, arg: usize) {
        rap_warn!(
            "In func {:?}, visitor checker error! Can't get {arg} in chain!",
            get_cleaned_def_path_name(self.tcx, self.def_id)
        );
        display_hashmap(&self.chains.variables, 1);
    }
}
