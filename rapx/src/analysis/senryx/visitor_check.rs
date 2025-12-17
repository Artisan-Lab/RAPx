use std::collections::HashSet;

use super::{
    contracts::abstract_state::AlignState,
    matcher::{UnsafeApi, get_arg_place},
    visitor::{BodyVisitor, CheckResult, PlaceTy},
};
use crate::{
    analysis::{
        core::{
            alias_analysis::AAResult,
            dataflow::{DataFlowAnalysis, default::DataFlowAnalyzer},
        },
        senryx::{
            contracts::property::{CisRange, CisRangeItem, PropertyContract},
            symbolic_analysis::{AnaOperand, SymbolicDef, verify_with_z3},
        },
        utils::fn_info::{
            display_hashmap, generate_contract_from_annotation_without_field_types,
            generate_contract_from_std_annotation_json, get_cleaned_def_path_name, get_pointee,
            is_ptr, is_ref, is_strict_ty_convert, reflect_generic,
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
use z3::ast::Ast;
use z3::ast::BV;

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
        rap_debug!("Check contract {:?} for {:?}.", contract, func_name);
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

    /// Taint Analysis: Check if the base pointer comes from a determined/aligned source.
    /// Sources considered determined/aligned:
    /// 1. References (Stack allocation) -> `&x`
    /// 2. AddressOf (Stack allocation) -> `&raw x`
    /// 3. Known aligned API calls -> `as_ptr`, `as_mut_ptr`, `alloc`
    fn is_base_determined(&self, base_local: usize) -> bool {
        if let Some(domain) = self.value_domains.get(&base_local) {
            if let Some(def) = &domain.def {
                match def {
                    SymbolicDef::Ref(_) => return true, // &T is aligned
                    SymbolicDef::Use(src) => return self.is_base_determined(*src), // Trace back
                    SymbolicDef::Cast(src, _) => return self.is_base_determined(*src), // Trace back
                    SymbolicDef::Call(func_name, _) => {
                        // Whitelist aligned allocation/access APIs
                        if func_name.contains("as_ptr")
                            || func_name.contains("as_mut_ptr")
                            || func_name.contains("alloc")
                        {
                            return true;
                        }
                    }
                    _ => {}
                }
            }
        }
        // Check VariableNode properties if SymbolicDef didn't give strict answer
        let points_to = self.chains.get_point_to_id(base_local);

        // If it points to a known Allocated object (not Unknown/Param), it's likely determined locally
        if points_to != base_local {
            if let Some(target_node) = self.chains.get_var_node(points_to) {
                // Check if target is a local stack variable (id < local_len)
                if self.chains.is_local(target_node.id) {
                    return true;
                }
            }
        }

        false
    }

    //  ------- End: Align checking functions -------

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

/// Impl block for Align check
/// Align checking functions
impl<'tcx> BodyVisitor<'tcx> {
    // Main API for align check
    pub fn check_align(&self, arg: usize, contract_required_ty: Ty<'tcx>) -> bool {
        let required_ty_layout = self.visit_ty_and_get_layout(contract_required_ty);
        if self.check_align_from_cis(arg, &required_ty_layout) {
            return true;
        }
        // check offset
        if let Some((op, base_local, offset_op, stride_layout)) = self.get_ptr_offset_info(arg) {
            return self.check_offset_align_with_z3(
                op,
                base_local,
                offset_op,
                stride_layout,
                contract_required_ty,
            );
        }

        // If no offset or cannot derive, try direct type casting check
        self.check_align_directly(arg, required_ty_layout)
    }

    /// First check for Align.
    /// If this var has contextual invariant state (cis), like:
    ///      #[rapx::proof::Align::(x, usize)]
    ///      pub fn test(x: *const usize) { ... }
    /// CIS will record 'x: Align(usize)' information for align check
    fn check_align_from_cis(&self, arg: usize, required_layout: &PlaceTy<'tcx>) -> bool {
        if let Some(var) = self.chains.get_var_node(arg) {
            for cis in &var.cis.contracts {
                if let PropertyContract::Align(cis_ty) = cis {
                    let cis_layout = self.visit_ty_and_get_layout(*cis_ty);
                    if Self::two_types_cast_check(cis_layout, required_layout.clone()) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Second check for Align.
    /// If no offset, check the type of ptr an its pointed object's type directly
    fn check_align_directly(&self, pointer_id: usize, required_ty: PlaceTy<'tcx>) -> bool {
        if let Some(pointee) = self.chains.get_obj_ty_through_chain(pointer_id) {
            let pointee_ty = self.visit_ty_and_get_layout(pointee);
            let pointer = self.chains.get_var_node(pointer_id).unwrap();

            // If the pointer has an explicitly recorded aligned state
            if let AlignState::Aligned(_) = pointer.ots.align {
                return Self::two_types_cast_check(pointee_ty, required_ty);
            }
        }
        false
    }

    /// Third check for Align.
    /// If ptr has Offset, use Z3 to solve constraints.
    /// Assuming `offset_op` is the accumulated offset from `base_local`.
    fn check_offset_align_with_z3(
        &self,
        op: BinOp,
        base_local: usize,
        offset_op: AnaOperand,
        stride_layout: PlaceTy<'tcx>,
        contract_required_ty: Ty<'tcx>,
    ) -> bool {
        // 1. get target type (Req) layout and alignment requirements
        let req_layout = self.visit_ty_and_get_layout(contract_required_ty);
        let mut req_aligns = req_layout.possible_aligns();

        // handle generic types: if target is generic and has no alignment constraints, check all common alignments (1~64)
        if let PlaceTy::GenericTy(..) = req_layout {
            if req_aligns.is_empty() {
                req_aligns.extend([1, 2, 4, 8, 16, 32, 64]);
            }
        }

        // opt: if only alignment 1 is required, it's always safe
        if req_aligns.len() == 1 && req_aligns.contains(&1) {
            return true;
        }

        // 2. get base node
        let base_node = if let Some(node) = self.chains.get_var_node(base_local) {
            node
        } else {
            return false;
        };

        // if base type is unknown, cannot assume base is aligned
        let base_pointee_ty = if let Some(ty) = base_node.ty {
            // Note: here we need the pointee type, not the pointer type itself
            crate::analysis::utils::fn_info::get_pointee(ty)
        } else {
            return false;
        };

        let base_layout = self.visit_ty_and_get_layout(base_pointee_ty);
        let mut base_aligns = base_layout.possible_aligns();

        // handle generic types: Base is also generic, extend its possible alignments
        if let PlaceTy::GenericTy(..) = base_layout {
            if base_aligns.is_empty() {
                base_aligns.extend([1, 2, 4, 8, 16, 32, 64]);
            }
        }

        rap_warn!(
            "Z3 Align Check: base_{} {:?} (aligns {:?}) {:?} offset (stride {:?}) => req_aligns {:?}",
            base_local,
            op,
            base_aligns,
            op,
            stride_layout,
            req_aligns
        );

        verify_with_z3(
            self.value_domains.clone(),
            self.path_constraints.clone(),
            |ctx, vars| {
                let bv_zero = BV::from_u64(ctx, 0, 64);

                // Model Base address
                let bv_base = if let Some(b) = vars.get(&base_local) {
                    b.clone()
                } else {
                    // if base address is not available, return false
                    return z3::ast::Bool::from_bool(ctx, false);
                };

                // Model Index
                let bv_index = match &offset_op {
                    AnaOperand::Local(idx) => {
                        if let Some(v) = vars.get(idx) {
                            v.clone()
                        } else {
                            BV::from_u64(ctx, 0, 64)
                        }
                    }
                    AnaOperand::Const(val) => BV::from_u64(ctx, *val as u64, 64),
                };

                // Model Stride
                let possible_strides: Vec<u64> = match &stride_layout {
                    PlaceTy::Ty(_, size) => vec![*size as u64],
                    PlaceTy::GenericTy(_, _, layout_set) => {
                        if layout_set.is_empty() {
                            // Generic type with no size constraints, check all common strides
                            vec![1, 2, 4, 8, 16, 32, 64]
                        } else {
                            layout_set.iter().map(|(_, size)| *size as u64).collect()
                        }
                    }
                    PlaceTy::Unknown => vec![1],
                };

                let mut constraints = Vec::new();

                // Coupling check: are Req and Base the same generic parameter?
                let is_same_generic = match (&req_layout, &base_layout) {
                    (PlaceTy::GenericTy(n1, _, _), PlaceTy::GenericTy(n2, _, _)) => n1 == n2,
                    _ => false,
                };

                // check all Strides
                for stride in possible_strides {
                    let bv_stride = BV::from_u64(ctx, stride, 64);
                    let bv_byte_offset = bv_index.bvmul(&bv_stride);

                    // Model Result Pointer
                    let result_ptr = match op {
                        BinOp::Add => bv_base.bvadd(&bv_byte_offset),
                        BinOp::Sub => bv_base.bvsub(&bv_byte_offset),
                        _ => bv_base.bvadd(&bv_byte_offset), // default Add
                    };

                    if is_same_generic {
                        // Same generic type: if Base satisfies alignment A, result must also satisfy A
                        for align in &req_aligns {
                            let bv_align = BV::from_u64(ctx, *align as u64, 64);

                            // Precondition
                            let base_is_aligned = bv_base.bvurem(&bv_align)._eq(&bv_zero);
                            // Postcondition
                            let result_aligned = result_ptr.bvurem(&bv_align)._eq(&bv_zero);

                            constraints.push(base_is_aligned.implies(&result_aligned));
                        }
                    } else {
                        // Different types: Base satisfies its own alignment => Result satisfies target alignment
                        for b_align in &base_aligns {
                            for r_align in &req_aligns {
                                let bv_base_align = BV::from_u64(ctx, *b_align as u64, 64);
                                let bv_req_align = BV::from_u64(ctx, *r_align as u64, 64);

                                let base_is_aligned = bv_base.bvurem(&bv_base_align)._eq(&bv_zero);
                                let result_aligned = result_ptr.bvurem(&bv_req_align)._eq(&bv_zero);

                                constraints.push(base_is_aligned.implies(&result_aligned));
                            }
                        }
                    }
                }

                if constraints.is_empty() {
                    // No constraints generated, return false
                    return z3::ast::Bool::from_bool(ctx, false);
                }

                // Must satisfy all generated constraints (AND)
                let constraints_refs: Vec<&z3::ast::Bool> = constraints.iter().collect();
                z3::ast::Bool::and(ctx, &constraints_refs)
            },
        )
    }

    // If the arg has offset from its pointed object, this function will return:
    fn get_ptr_offset_info(&self, arg: usize) -> Option<(BinOp, usize, AnaOperand, PlaceTy<'tcx>)> {
        if let Some(domain) = self.chains.get_var_node(arg) {
            if let Some(def) = &domain.offset_from {
                match def {
                    SymbolicDef::PtrOffset(op, base, off, place_ty) => {
                        return Some((*op, *base, off.clone(), place_ty.clone()));
                    }
                    _ => {}
                }
            }
        }
        None
    }

    /// Updates the alignment state of the given local variable.
    /// is_aligned = true  -> Aligned
    /// is_aligned = false -> Unaligned
    pub fn update_align_state(&mut self, ptr_local: usize, is_aligned: bool) {
        // Get type info
        let ptr_ty_opt = self.chains.get_var_node(ptr_local).and_then(|n| n.ty);

        if let Some(ptr_ty) = ptr_ty_opt {
            if is_ptr(ptr_ty) || is_ref(ptr_ty) {
                let pointee_ty = get_pointee(ptr_ty);

                if let Some(ptr_node) = self.chains.get_var_node_mut(ptr_local) {
                    if is_aligned {
                        ptr_node.ots.align = AlignState::Aligned(pointee_ty);
                        rap_debug!(
                            "Refine State: _{} (source) marked as Aligned({:?}) via condition (True).",
                            ptr_local,
                            pointee_ty
                        );
                    } else {
                        ptr_node.ots.align = AlignState::Unaligned(pointee_ty);

                        rap_debug!(
                            "Refine State: _{} (source) marked as Unaligned({:?}) via condition (False).",
                            ptr_local,
                            pointee_ty
                        );
                    }
                }
            }
        }
    }

    /// Checks if the argument satisfies the alignment requirements of the contract.
    /// Retrieves the pre-computed state from the graph and compares types.
    pub fn check_align_by_pre_computed_state(
        &self,
        arg: usize,
        contract_required_ty: Ty<'tcx>,
    ) -> bool {
        // 1. Retrieve the variable node from the graph
        if let Some(var) = self.chains.get_var_node(arg) {
            // 2. Check if the state is marked as 'Aligned'
            if let AlignState::Aligned(state_ty) = var.ots.align {
                // 3. Compare the state's recorded type with the contract's required type
                // We assume the pointer is aligned for `state_ty`. We must ensure
                // `state_ty` alignment implies `contract_required_ty` alignment.
                let state_layout = self.visit_ty_and_get_layout(state_ty);
                let req_layout = self.visit_ty_and_get_layout(contract_required_ty);

                rap_warn!(
                    "Check Align: arg_{} StateTy: {:?} vs ReqTy: {:?}",
                    arg,
                    state_layout,
                    req_layout
                );

                // True if Src alignment requirements >= Dest alignment requirements
                return Self::two_types_cast_check(state_layout, req_layout);
            } else {
                rap_warn!("Check Align: arg_{} is Unaligned or Unknown", arg);
            }
        } else {
            rap_warn!("Check Align: arg_{} node not found", arg);
        }
        false
    }

    // Helper function: check whether type cast is aligned.
    fn two_types_cast_check(src: PlaceTy<'tcx>, dest: PlaceTy<'tcx>) -> bool {
        let src_aligns = src.possible_aligns();
        let dest_aligns = dest.possible_aligns();
        if dest_aligns.len() == 0 && src != dest {
            // dst ty could be arbitrary type && src and dst are different types
            return false;
        }

        for &d_align in &dest_aligns {
            if d_align != 1 && src_aligns.len() == 0 {
                // src ty could be arbitrary type
                return false;
            }
            for &s_align in &src_aligns {
                if s_align < d_align {
                    return false;
                }
            }
        }
        true
    }

    /// Attempts to prove a stricter alignment for the base pointer using Z3 and path constraints.
    fn try_refine_alignment(&self, base_local: usize, current_align: u64) -> u64 {
        // Check alignments in descending order: 64, 32, 16, 8, 4
        for candidate in [64, 32, 16, 8, 4] {
            if candidate <= current_align {
                break;
            }

            let is_proven = verify_with_z3(
                self.value_domains.clone(),
                self.path_constraints.clone(),
                |ctx, vars| {
                    if let Some(bv_base) = vars.get(&base_local) {
                        let bv_cand = BV::from_u64(ctx, candidate, 64);
                        let bv_zero = BV::from_u64(ctx, 0, 64);
                        // Prove: base % candidate == 0
                        bv_base.bvurem(&bv_cand)._eq(&bv_zero)
                    } else {
                        z3::ast::Bool::from_bool(ctx, false)
                    }
                },
            );

            if is_proven {
                rap_warn!(
                    "Refine Align: Successfully refined base_{} to align {}",
                    base_local,
                    candidate
                );
                return candidate;
            }
        }
        current_align
    }

    /// Checks if the offset is a multiple of the required alignment using Z3.
    fn check_offset_is_aligned(&self, _base_local: usize, offset: &AnaOperand, align: u64) -> bool {
        verify_with_z3(
            self.value_domains.clone(),
            self.path_constraints.clone(),
            |ctx, vars| {
                let bv_align = BV::from_u64(ctx, align, 64);
                let bv_zero = BV::from_u64(ctx, 0, 64);

                let bv_offset = match offset {
                    AnaOperand::Local(idx) => {
                        if let Some(v) = vars.get(idx) {
                            v.clone()
                        } else {
                            BV::from_u64(ctx, 0, 64)
                        }
                    }
                    AnaOperand::Const(val) => BV::from_u64(ctx, *val as u64, 64),
                };

                // Prove: offset % align == 0
                bv_offset.bvurem(&bv_align)._eq(&bv_zero)
            },
        )
    }

    /// Checks if (AccumulatedDef + CurrentOp) % Align == 0 using Z3.
    fn check_cumulative_offset_aligned(
        &self,
        _base_local: usize,
        acc_def: &SymbolicDef,
        curr_op: &AnaOperand,
        align: u64,
    ) -> bool {
        verify_with_z3(
            self.value_domains.clone(),
            self.path_constraints.clone(),
            |ctx, vars| {
                let bv_align = BV::from_u64(ctx, align, 64);
                let bv_zero = BV::from_u64(ctx, 0, 64);
                let bv_acc = self.symbolic_def_to_bv(ctx, vars, acc_def);
                let bv_curr = match curr_op {
                    AnaOperand::Local(idx) => {
                        if let Some(v) = vars.get(idx) {
                            v.clone()
                        } else {
                            BV::from_u64(ctx, 0, 64)
                        }
                    }
                    AnaOperand::Const(val) => BV::from_u64(ctx, *val as u64, 64),
                };
                let total = bv_acc.bvadd(&bv_curr);
                // Prove: (acc + curr) % align == 0
                total.bvurem(&bv_align)._eq(&bv_zero)
            },
        )
    }

    // Helper: Converts Operand to SymbolicDef
    fn operand_to_symbolic_def(&self, op: AnaOperand) -> SymbolicDef<'tcx> {
        match op {
            AnaOperand::Local(l) => SymbolicDef::Use(l),
            AnaOperand::Const(c) => SymbolicDef::Constant(c),
        }
    }

    // Helper: Combines two offsets into a SymbolicDef (Simplified)
    fn combine_offsets(&self, def: SymbolicDef<'tcx>, op: AnaOperand) -> SymbolicDef<'tcx> {
        match (def, op) {
            (SymbolicDef::Constant(c1), AnaOperand::Const(c2)) => SymbolicDef::Constant(c1 + c2),
            (SymbolicDef::Use(l), o) => SymbolicDef::Binary(BinOp::Add, l, o),
            (d, _) => d,
        }
    }

    // Helper: Converts SymbolicDef to Z3 BitVector
    fn symbolic_def_to_bv<'a>(
        &self,
        ctx: &'a z3::Context,
        vars: &std::collections::HashMap<usize, BV<'a>>,
        def: &SymbolicDef,
    ) -> BV<'a> {
        match def {
            SymbolicDef::Constant(c) => BV::from_u64(ctx, *c as u64, 64),
            SymbolicDef::Use(l) => vars.get(l).cloned().unwrap_or(BV::from_u64(ctx, 0, 64)),
            SymbolicDef::Binary(op, lhs, rhs) => {
                let lhs_bv = vars.get(lhs).cloned().unwrap_or(BV::from_u64(ctx, 0, 64));
                let rhs_bv = match rhs {
                    AnaOperand::Local(l) => {
                        vars.get(l).cloned().unwrap_or(BV::from_u64(ctx, 0, 64))
                    }
                    AnaOperand::Const(c) => BV::from_u64(ctx, *c as u64, 64),
                };
                match op {
                    BinOp::Add => lhs_bv.bvadd(&rhs_bv),
                    _ => BV::from_u64(ctx, 0, 64),
                }
            }
            _ => BV::from_u64(ctx, 0, 64),
        }
    }
}
