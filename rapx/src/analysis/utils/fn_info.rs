#[allow(unused)]
use crate::analysis::senryx::contracts::property::PropertyContract;
use crate::analysis::senryx::matcher::parse_unsafe_api;
use crate::analysis::unsafety_isolation::generate_dot::NodeType;
use crate::rap_debug;
use crate::rap_warn;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::Attribute;
use rustc_hir::ImplItemKind;
use rustc_middle::mir::BinOp;
use rustc_middle::mir::Local;
use rustc_middle::mir::{BasicBlock, Terminator};
use rustc_middle::ty::{AssocKind, Mutability, Ty, TyCtxt, TyKind};
use rustc_middle::{
    mir::{Operand, TerminatorKind},
    ty,
};
use rustc_span::def_id::LocalDefId;
use rustc_span::kw;
use rustc_span::sym;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;
use syn::Expr;

pub fn generate_node_ty(tcx: TyCtxt, def_id: DefId) -> NodeType {
    (def_id, check_safety(tcx, def_id), get_type(tcx, def_id))
}

pub fn check_visibility(tcx: TyCtxt, func_defid: DefId) -> bool {
    if !tcx.visibility(func_defid).is_public() {
        return false;
    }
    // if func_defid.is_local() {
    //     if let Some(local_defid) = func_defid.as_local() {
    //         let module_moddefid = tcx.parent_module_from_def_id(local_defid);
    //         let module_defid = module_moddefid.to_def_id();
    //         if !tcx.visibility(module_defid).is_public() {
    //             // println!("module def id {:?}",UigUnit::get_cleaned_def_path_name(tcx, module_defid));
    //             return Self::is_re_exported(tcx, func_defid, module_moddefid.to_local_def_id());
    //         }
    //     }
    // }
    true
}

pub fn is_re_exported(tcx: TyCtxt, target_defid: DefId, module_defid: LocalDefId) -> bool {
    for child in tcx.module_children_local(module_defid) {
        if child.vis.is_public() {
            if let Some(def_id) = child.res.opt_def_id() {
                if def_id == target_defid {
                    return true;
                }
            }
        }
    }
    false
}

pub fn print_hashset<T: std::fmt::Debug>(set: &HashSet<T>) {
    for item in set {
        println!("{:?}", item);
    }
    println!("---------------");
}

pub fn get_cleaned_def_path_name(tcx: TyCtxt, def_id: DefId) -> String {
    let def_id_str = format!("{:?}", def_id);
    let mut parts: Vec<&str> = def_id_str.split("::").collect();

    let mut remove_first = false;
    if let Some(first_part) = parts.get_mut(0) {
        if first_part.contains("core") {
            *first_part = "core";
        } else if first_part.contains("std") {
            *first_part = "std";
        } else if first_part.contains("alloc") {
            *first_part = "alloc";
        } else {
            remove_first = true;
        }
    }
    if remove_first && !parts.is_empty() {
        parts.remove(0);
    }

    let new_parts: Vec<String> = parts
        .into_iter()
        .filter_map(|s| {
            if s.contains("{") {
                if remove_first {
                    get_struct_name(tcx, def_id)
                } else {
                    None
                }
            } else {
                Some(s.to_string())
            }
        })
        .collect();

    let mut cleaned_path = new_parts.join("::");
    cleaned_path = cleaned_path.trim_end_matches(')').to_string();
    cleaned_path
}

pub fn get_sp_json() -> serde_json::Value {
    let json_data: serde_json::Value =
        serde_json::from_str(include_str!("../unsafety_isolation/data/std_sps.json"))
            .expect("Unable to parse JSON");
    json_data
}

pub fn get_std_api_signature_json() -> serde_json::Value {
    let json_data: serde_json::Value =
        serde_json::from_str(include_str!("../unsafety_isolation/data/std_sig.json"))
            .expect("Unable to parse JSON");
    json_data
}

pub fn get_sp(tcx: TyCtxt<'_>, def_id: DefId) -> HashSet<String> {
    let cleaned_path_name = get_cleaned_def_path_name(tcx, def_id);
    let json_data: serde_json::Value = get_sp_json();

    if let Some(function_info) = json_data.get(&cleaned_path_name) {
        if let Some(sp_list) = function_info.get("0") {
            let mut result = HashSet::new();
            if let Some(sp_array) = sp_list.as_array() {
                for sp in sp_array {
                    if let Some(sp_name) = sp.as_str() {
                        result.insert(sp_name.to_string());
                    }
                }
            }
            return result;
        }
    }
    HashSet::new()
}

pub fn get_struct_name(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        if let Some(impl_id) = assoc_item.impl_container(tcx) {
            let ty = tcx.type_of(impl_id).skip_binder();
            let type_name = ty.to_string();
            let struct_name = type_name
                .split('<')
                .next()
                .unwrap_or("")
                .split("::")
                .last()
                .unwrap_or("")
                .to_string();

            return Some(struct_name);
        }
    }
    None
}

pub fn check_safety(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let poly_fn_sig = tcx.fn_sig(def_id);
    let fn_sig = poly_fn_sig.skip_binder();
    fn_sig.safety() == rustc_hir::Safety::Unsafe
}

//retval: 0-constructor, 1-method, 2-function
pub fn get_type(tcx: TyCtxt<'_>, def_id: DefId) -> usize {
    let mut node_type = 2;
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        match assoc_item.kind {
            AssocKind::Fn { has_self, .. } => {
                if has_self {
                    node_type = 1;
                } else {
                    let fn_sig = tcx.fn_sig(def_id).skip_binder();
                    let output = fn_sig.output().skip_binder();
                    // return type is 'Self'
                    if output.is_param(0) {
                        node_type = 0;
                    }
                    // return type is struct's name
                    if let Some(impl_id) = assoc_item.impl_container(tcx) {
                        let ty = tcx.type_of(impl_id).skip_binder();
                        if output == ty {
                            node_type = 0;
                        }
                    }
                    match output.kind() {
                        TyKind::Ref(_, ref_ty, _) => {
                            if ref_ty.is_param(0) {
                                node_type = 0;
                            }
                            if let Some(impl_id) = assoc_item.impl_container(tcx) {
                                let ty = tcx.type_of(impl_id).skip_binder();
                                if *ref_ty == ty {
                                    node_type = 0;
                                }
                            }
                        }
                        TyKind::Adt(adt_def, substs) => {
                            if adt_def.is_enum()
                                && (tcx.is_diagnostic_item(sym::Option, adt_def.did())
                                    || tcx.is_diagnostic_item(sym::Result, adt_def.did())
                                    || tcx.is_diagnostic_item(kw::Box, adt_def.did()))
                            {
                                let inner_ty = substs.type_at(0);
                                if inner_ty.is_param(0) {
                                    node_type = 0;
                                }
                                if let Some(impl_id) = assoc_item.impl_container(tcx) {
                                    let ty_impl = tcx.type_of(impl_id).skip_binder();
                                    if inner_ty == ty_impl {
                                        node_type = 0;
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => todo!(),
        }
    }
    node_type
}

pub fn get_adt_ty(tcx: TyCtxt, def_id: DefId) -> Option<Ty> {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        if let Some(impl_id) = assoc_item.impl_container(tcx) {
            return Some(tcx.type_of(impl_id).skip_binder());
        }
    }
    None
}

pub fn get_cons(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<NodeType> {
    let mut cons = Vec::new();
    if tcx.def_kind(def_id) == DefKind::Fn || get_type(tcx, def_id) == 0 {
        return cons;
    }
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        if let Some(impl_id) = assoc_item.impl_container(tcx) {
            // get struct ty
            let ty = tcx.type_of(impl_id).skip_binder();
            if let Some(adt_def) = ty.ty_adt_def() {
                let adt_def_id = adt_def.did();
                let impls = tcx.inherent_impls(adt_def_id);
                for impl_def_id in impls {
                    for item in tcx.associated_item_def_ids(impl_def_id) {
                        if (tcx.def_kind(item) == DefKind::Fn
                            || tcx.def_kind(item) == DefKind::AssocFn)
                            && get_type(tcx, *item) == 0
                        {
                            cons.push(generate_node_ty(tcx, *item));
                        }
                    }
                }
            }
        }
    }
    cons
}

pub fn get_callees(tcx: TyCtxt<'_>, def_id: DefId) -> HashSet<DefId> {
    let mut callees = HashSet::new();
    if tcx.is_mir_available(def_id) {
        let body = tcx.optimized_mir(def_id);
        for bb in body.basic_blocks.iter() {
            if let TerminatorKind::Call { func, .. } = &bb.terminator().kind {
                if let Operand::Constant(func_constant) = func {
                    if let ty::FnDef(ref callee_def_id, _) = func_constant.const_.ty().kind() {
                        if check_safety(tcx, *callee_def_id)
                        // && check_visibility(tcx, *callee_def_id)
                        {
                            let sp_set = get_sp(tcx, *callee_def_id);
                            if sp_set.len() != 0 {
                                callees.insert(*callee_def_id);
                            }
                        }
                    }
                }
            }
        }
    }
    callees
}

// return all the impls def id of corresponding struct
pub fn get_impls_for_struct(tcx: TyCtxt<'_>, struct_def_id: DefId) -> Vec<DefId> {
    let mut impls = Vec::new();
    for impl_item_id in tcx.hir_crate_items(()).impl_items() {
        let impl_item = tcx.hir_impl_item(impl_item_id);
        match impl_item.kind {
            ImplItemKind::Type(ty) => {
                if let rustc_hir::TyKind::Path(ref qpath) = ty.kind {
                    if let rustc_hir::QPath::Resolved(_, path) = qpath {
                        if let rustc_hir::def::Res::Def(_, ref def_id) = path.res {
                            if *def_id == struct_def_id {
                                impls.push(impl_item.owner_id.to_def_id());
                            }
                        }
                    }
                }
            }
            _ => (),
        }
    }
    impls
}

pub fn get_adt_def_id_by_adt_method(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        if let Some(impl_id) = assoc_item.impl_container(tcx) {
            // get struct ty
            let ty = tcx.type_of(impl_id).skip_binder();
            if let Some(adt_def) = ty.ty_adt_def() {
                return Some(adt_def.did());
            }
        }
    }
    None
}

// get the pointee or wrapped type
pub fn get_pointee(matched_ty: Ty<'_>) -> Ty<'_> {
    // progress_info!("get_pointee: > {:?} as type: {:?}", matched_ty, matched_ty.kind());
    let pointee = if let ty::RawPtr(ty_mut, _) = matched_ty.kind() {
        get_pointee(*ty_mut)
    } else if let ty::Ref(_, referred_ty, _) = matched_ty.kind() {
        get_pointee(*referred_ty)
    } else {
        matched_ty
    };
    pointee
}

pub fn is_ptr(matched_ty: Ty<'_>) -> bool {
    if let ty::RawPtr(_, _) = matched_ty.kind() {
        return true;
    }
    false
}

pub fn is_ref(matched_ty: Ty<'_>) -> bool {
    if let ty::Ref(_, _, _) = matched_ty.kind() {
        return true;
    }
    false
}

pub fn is_slice(matched_ty: Ty) -> Option<Ty> {
    if let ty::Slice(inner) = matched_ty.kind() {
        return Some(*inner);
    }
    None
}

pub fn has_mut_self_param(tcx: TyCtxt, def_id: DefId) -> bool {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        match assoc_item.kind {
            AssocKind::Fn { has_self, .. } => {
                if has_self {
                    let body = tcx.optimized_mir(def_id);
                    let fst_arg = body.local_decls[Local::from_usize(1)].clone();
                    let ty = fst_arg.ty;
                    let is_mut_ref =
                        matches!(ty.kind(), ty::Ref(_, _, mutbl) if *mutbl == Mutability::Mut);
                    return fst_arg.mutability.is_mut() || is_mut_ref;
                }
            }
            _ => (),
        }
    }
    false
}

// Input the adt def id
// Return set of (mutable method def_id, fields can be modified)
pub fn get_all_mutable_methods(tcx: TyCtxt, def_id: DefId) -> HashMap<DefId, HashSet<usize>> {
    let mut results = HashMap::new();
    let adt_def = get_adt_def_id_by_adt_method(tcx, def_id);
    let public_fields = adt_def.map_or_else(HashSet::new, |def| get_public_fields(tcx, def));
    let impl_vec = adt_def.map_or_else(Vec::new, |def| get_impls_for_struct(tcx, def));
    for impl_id in impl_vec {
        let associated_items = tcx.associated_items(impl_id);
        for item in associated_items.in_definition_order() {
            if let AssocKind::Fn {
                name: _,
                has_self: _,
            } = item.kind
            {
                let item_def_id = item.def_id;
                if has_mut_self_param(tcx, item_def_id) {
                    // TODO: using dataflow to detect field modificaiton, combined with public fields
                    let modified_fields = public_fields.clone();
                    results.insert(item_def_id, modified_fields);
                }
            }
        }
    }
    results
}

// Check each field's visibility, return the public fields vec
pub fn get_public_fields(tcx: TyCtxt, def_id: DefId) -> HashSet<usize> {
    let adt_def = tcx.adt_def(def_id);
    adt_def
        .all_fields()
        .enumerate()
        .filter_map(|(index, field_def)| tcx.visibility(field_def.did).is_public().then_some(index))
        .collect()
}

// general function for displaying hashmap
pub fn display_hashmap<K, V>(map: &HashMap<K, V>, level: usize)
where
    K: Ord + Debug + Hash,
    V: Debug,
{
    let indent = "  ".repeat(level);
    let mut sorted_keys: Vec<_> = map.keys().collect();
    sorted_keys.sort();

    for key in sorted_keys {
        if let Some(value) = map.get(key) {
            println!("{}{:?}: {:?}", indent, key, value);
        }
    }
}

pub fn get_all_std_unsafe_callees(tcx: TyCtxt, def_id: DefId) -> Vec<String> {
    let mut results = Vec::new();
    let body = tcx.optimized_mir(def_id);
    let bb_len = body.basic_blocks.len();
    for i in 0..bb_len {
        let callees = match_std_unsafe_callee(
            tcx,
            body.basic_blocks[BasicBlock::from_usize(i)]
                .clone()
                .terminator(),
        );
        results.extend(callees);
    }
    results
}

pub fn get_all_std_unsafe_callees_block_id(tcx: TyCtxt, def_id: DefId) -> Vec<usize> {
    let mut results = Vec::new();
    let body = tcx.optimized_mir(def_id);
    let bb_len = body.basic_blocks.len();
    for i in 0..bb_len {
        if match_std_unsafe_callee(
            tcx,
            body.basic_blocks[BasicBlock::from_usize(i)]
                .clone()
                .terminator(),
        )
        .is_empty()
        {
            results.push(i);
        }
    }
    results
}

pub fn match_std_unsafe_callee(tcx: TyCtxt<'_>, terminator: &Terminator<'_>) -> Vec<String> {
    let mut results = Vec::new();
    if let TerminatorKind::Call { func, .. } = &terminator.kind {
        if let Operand::Constant(func_constant) = func {
            if let ty::FnDef(ref callee_def_id, _raw_list) = func_constant.const_.ty().kind() {
                let func_name = get_cleaned_def_path_name(tcx, *callee_def_id);
                if parse_unsafe_api(&func_name).is_some() {
                    results.push(func_name);
                }
            }
        }
    }
    results
}

// Bug definition: (1) strict -> weak & dst is mutable;
//                 (2) _ -> strict
pub fn is_strict_ty_convert<'tcx>(tcx: TyCtxt<'tcx>, src_ty: Ty<'tcx>, dst_ty: Ty<'tcx>) -> bool {
    (is_strict_ty(tcx, src_ty) && dst_ty.is_mutable_ptr()) || is_strict_ty(tcx, dst_ty)
}

// strict ty: bool, str, adt fields containing bool or str;
pub fn is_strict_ty<'tcx>(tcx: TyCtxt<'tcx>, ori_ty: Ty<'tcx>) -> bool {
    let ty = get_pointee(ori_ty);
    let mut flag = false;
    if let TyKind::Adt(adt_def, substs) = ty.kind() {
        if adt_def.is_struct() {
            for field_def in adt_def.all_fields() {
                flag |= is_strict_ty(tcx, field_def.ty(tcx, substs))
            }
        }
    }
    ty.is_bool() || ty.is_str() || flag
}

pub fn reverse_op(op: BinOp) -> BinOp {
    match op {
        BinOp::Lt => BinOp::Ge,
        BinOp::Ge => BinOp::Lt,
        BinOp::Le => BinOp::Gt,
        BinOp::Gt => BinOp::Le,
        BinOp::Eq => BinOp::Eq,
        BinOp::Ne => BinOp::Ne,
        _ => op,
    }
}

/// Same with `generate_contract_from_annotation` but does not contain field types.
pub fn generate_contract_from_annotation_without_field_types(
    tcx: TyCtxt,
    def_id: DefId,
) -> Vec<(usize, Vec<usize>, PropertyContract)> {
    let contracts_with_ty = generate_contract_from_annotation(tcx, def_id);

    contracts_with_ty
        .into_iter()
        .map(|(local_id, fields_with_ty, contract)| {
            let fields: Vec<usize> = fields_with_ty
                .into_iter()
                .map(|(field_idx, _)| field_idx)
                .collect();
            (local_id, fields, contract)
        })
        .collect()
}

/// Filter the function which contains "rapx::proof"
pub fn is_verify_target_func(tcx: TyCtxt, def_id: DefId) -> bool {
    const REGISTER_TOOL: &str = "rapx";
    for attr in tcx.get_all_attrs(def_id).into_iter() {
        if let Attribute::Unparsed(tool_attr) = attr {
            if tool_attr.path.segments[0].as_str() == REGISTER_TOOL
                && tool_attr.path.segments[1].as_str() == "proof"
            {
                return true;
            }
        }
    }
    false
}

/// Get the annotation in tag-std style.
/// Then generate the contractual invariant states (CIS) for the args.
/// This function will recognize the args name and record states to MIR variable (represent by usize).
/// Return value means Vec<(local_id, fields of this local, contracts)>
pub fn generate_contract_from_annotation(
    tcx: TyCtxt,
    def_id: DefId,
) -> Vec<(usize, Vec<(usize, Ty)>, PropertyContract)> {
    const REGISTER_TOOL: &str = "rapx";
    let tool_attrs = tcx.get_all_attrs(def_id).into_iter().filter(|attr| {
        if let Attribute::Unparsed(tool_attr) = attr {
            if tool_attr.path.segments[0].as_str() == REGISTER_TOOL
                && tool_attr.path.segments[1].as_str() != "proof"
            {
                return true;
            }
        }
        false
    });
    let mut results = Vec::new();
    for attr in tool_attrs {
        let attr_str = rustc_hir_pretty::attribute_to_string(&tcx, attr);
        let safety_attr =
            safety_parser::property_attr::parse_inner_attr_from_str(attr_str.as_str()).unwrap();
        let attr_name = safety_attr.name;
        let attr_kind = safety_attr.kind;
        let contract = PropertyContract::new(tcx, def_id, attr_kind, attr_name, &safety_attr.expr);
        let (local, fields) = parse_cis_local(tcx, def_id, safety_attr.expr);
        results.push((local, fields, contract));
    }
    // if results.len() > 0 {
    //     rap_warn!("results:\n{:?}", results);
    // }
    results
}

/// Parse attr.expr into local id and local fields.
///
/// Example:
/// ```
/// #[rapx::inner(property = ValidPtr(ptr, u32, 1), kind = "precond")]
/// #[rapx::inner(property = ValidNum(region.size>=0), kind = "precond")]
/// pub fn xor_secret_region(ptr: *mut u32, region:SecretRegion) -> u32 {...}
/// ```
///
/// The first attribute will be parsed as (1, []).
///     -> "1" means the first arg "ptr", "[]" means no fields.
/// The second attribute will be parsed as (2, [1]).
///     -> "2" means the second arg "region", "[1]" means "size" is region's second field.
///
/// If this function doesn't have args, then it will return default pattern: (0, Vec::new())
pub fn parse_cis_local(tcx: TyCtxt, def_id: DefId, expr: Vec<Expr>) -> (usize, Vec<(usize, Ty)>) {
    // match expr with cis local
    for e in expr {
        if let Some((base, fields, _ty)) = parse_expr_into_local_and_ty(tcx, def_id, &e) {
            return (base, fields);
        }
    }
    (0, Vec::new())
}

/// parse single expr into (local, fields, ty)
pub fn parse_expr_into_local_and_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    if let Some((base_ident, fields)) = access_ident_recursive(&expr) {
        let (param_names, param_tys) = parse_signature(tcx, def_id);
        if param_names[0] == "0".to_string() {
            return None;
        }
        if let Some(param_index) = param_names.iter().position(|name| name == &base_ident) {
            let mut current_ty = param_tys[param_index];
            let mut field_indices = Vec::new();
            for field_name in fields {
                // peel the ref and ptr
                let peeled_ty = current_ty.peel_refs();
                if let rustc_middle::ty::TyKind::Adt(adt_def, arg_list) = *peeled_ty.kind() {
                    let variant = adt_def.non_enum_variant();
                    // 1. if field_name is number, then parse it as usize
                    if let Ok(field_idx) = field_name.parse::<usize>() {
                        if field_idx < variant.fields.len() {
                            current_ty = variant.fields[rustc_abi::FieldIdx::from_usize(field_idx)]
                                .ty(tcx, arg_list);
                            field_indices.push((field_idx, current_ty));
                            continue;
                        }
                    }
                    // 2. if field_name is String, then compare it with current ty's field names
                    if let Some((idx, _)) = variant
                        .fields
                        .iter()
                        .enumerate()
                        .find(|(_, f)| f.ident(tcx).name.to_string() == field_name.clone())
                    {
                        current_ty =
                            variant.fields[rustc_abi::FieldIdx::from_usize(idx)].ty(tcx, arg_list);
                        field_indices.push((idx, current_ty));
                    }
                    // 3. if field_name can not match any fields, then break
                    else {
                        break; // TODO:
                    }
                }
                // if current ty is not Adt, then break the loop
                else {
                    break; // TODO:
                }
            }
            // It's different from default one, we return the result as param_index+1 because param_index count from 0.
            // But 0 in MIR is the ret index, the args' indexes begin from 1.
            return Some((param_index + 1, field_indices, current_ty));
        }
    }
    None
}

/// Return the Vecs of args' names and types
/// This function will handle outside def_id by different way.
pub fn parse_signature<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> (Vec<String>, Vec<Ty<'tcx>>) {
    // 0. If the def id is local
    if def_id.as_local().is_some() {
        return parse_local_signature(tcx, def_id);
    } else {
        rap_debug!("{:?} is not local def id.", def_id);
        return parse_outside_signature(tcx, def_id);
    };
}

/// Return the Vecs of args' names and types of outside functions.
fn parse_outside_signature<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> (Vec<String>, Vec<Ty<'tcx>>) {
    let sig = tcx.fn_sig(def_id).skip_binder();
    let param_tys: Vec<Ty<'tcx>> = sig.inputs().skip_binder().iter().copied().collect();

    // 1. check pre-defined std unsafe api signature
    if let Some(args_name) = get_known_std_names(tcx, def_id) {
        // rap_warn!(
        //     "function {:?} has arg: {:?}, arg types: {:?}",
        //     def_id,
        //     args_name,
        //     param_tys
        // );
        return (args_name, param_tys);
    }

    // 2. TODO: If can not find known std apis, then use numbers like `0`,`1`,... to represent args.
    let args_name = (0..param_tys.len()).map(|i| format!("{}", i)).collect();
    rap_debug!(
        "function {:?} has arg: {:?}, arg types: {:?}",
        def_id,
        args_name,
        param_tys
    );
    return (args_name, param_tys);
}

/// We use a json to record known std apis' arg names.
/// This function will search the json and return the names.
/// Notes: If std gets updated, the json may still record old ones.
fn get_known_std_names<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<Vec<String>> {
    let std_func_name = get_cleaned_def_path_name(tcx, def_id);
    let json_data: serde_json::Value = get_std_api_signature_json();

    if let Some(arg_info) = json_data.get(&std_func_name) {
        if let Some(args_name) = arg_info.as_array() {
            // set default value to arg name
            if args_name.len() == 0 {
                return Some(vec!["0".to_string()]);
            }
            // iterate and collect
            let mut result = Vec::new();
            for arg in args_name {
                if let Some(sp_name) = arg.as_str() {
                    result.push(sp_name.to_string());
                }
            }
            return Some(result);
        }
    }
    None
}

/// Return the Vecs of args' names and types of local functions.
pub fn parse_local_signature(tcx: TyCtxt, def_id: DefId) -> (Vec<String>, Vec<Ty>) {
    // 1. parse local def_id and get arg list
    let local_def_id = def_id.as_local().unwrap();
    let hir_body = tcx.hir_body_owned_by(local_def_id);
    if hir_body.params.len() == 0 {
        return (vec!["0".to_string()], Vec::new());
    }
    // 2. contruct the vec of param and param ty
    let params = hir_body.params;
    let typeck_results = tcx.typeck_body(hir_body.id());
    let mut param_names = Vec::new();
    let mut param_tys = Vec::new();
    for param in params {
        match param.pat.kind {
            rustc_hir::PatKind::Binding(_, _, ident, _) => {
                param_names.push(ident.name.to_string());
                let ty = typeck_results.pat_ty(param.pat);
                param_tys.push(ty);
            }
            _ => {
                param_names.push(String::new());
                param_tys.push(typeck_results.pat_ty(param.pat));
            }
        }
    }
    (param_names, param_tys)
}

/// return the (ident, its fields) of the expr.
///
/// illustrated cases :
///    ptr	-> ("ptr", [])
///    region.size	-> ("region", ["size"])
///    tuple.0.value -> ("tuple", ["0", "value"])
pub fn access_ident_recursive(expr: &Expr) -> Option<(String, Vec<String>)> {
    match expr {
        Expr::Path(syn::ExprPath { path, .. }) => {
            if path.segments.len() == 1 {
                rap_debug!("expr2 {:?}", expr);
                let ident = path.segments[0].ident.to_string();
                Some((ident, Vec::new()))
            } else {
                None
            }
        }
        // get the base and fields recursively
        Expr::Field(syn::ExprField { base, member, .. }) => {
            let (base_ident, mut fields) =
                if let Some((base_ident, fields)) = access_ident_recursive(base) {
                    (base_ident, fields)
                } else {
                    return None;
                };
            let field_name = match member {
                syn::Member::Named(ident) => ident.to_string(),
                syn::Member::Unnamed(index) => index.index.to_string(),
            };
            fields.push(field_name);
            Some((base_ident, fields))
        }
        _ => None,
    }
}

/// parse expr into number.
pub fn parse_expr_into_number(expr: &Expr) -> Option<usize> {
    if let Expr::Lit(expr_lit) = expr {
        if let syn::Lit::Int(lit_int) = &expr_lit.lit {
            return lit_int.base10_parse::<usize>().ok();
        }
    }
    None
}

/// Match a type identifier string to a concrete Rust type
///
/// This function attempts to match a given type identifier (e.g., "u32", "T", "MyStruct")
/// to a type in the provided parameter type list. It handles:
/// 1. Built-in primitive types (u32, usize, etc.)
/// 2. Generic type parameters (T, U, etc.)
/// 3. User-defined types found in the parameter list
///
/// Arguments:
/// - `tcx`: Type context for querying compiler information
/// - `type_ident`: String representing the type identifier to match
/// - `param_ty`: List of parameter types from the function signature
///
/// Returns:
/// - `Some(Ty)` if a matching type is found
/// - `None` if no match is found
pub fn match_ty_with_ident(tcx: TyCtxt, def_id: DefId, type_ident: String) -> Option<Ty> {
    // 1. First check for built-in primitive types
    if let Some(primitive_ty) = match_primitive_type(tcx, type_ident.clone()) {
        return Some(primitive_ty);
    }
    // 2. Check if the identifier matches any generic type parameter
    return find_generic_param(tcx, def_id, type_ident.clone());
    // 3. Check if the identifier matches any user-defined type in the parameters
    // find_user_defined_type(tcx, def_id, type_ident)
}

/// Match built-in primitive types from String
fn match_primitive_type(tcx: TyCtxt, type_ident: String) -> Option<Ty> {
    match type_ident.as_str() {
        "i8" => Some(tcx.types.i8),
        "i16" => Some(tcx.types.i16),
        "i32" => Some(tcx.types.i32),
        "i64" => Some(tcx.types.i64),
        "i128" => Some(tcx.types.i128),
        "isize" => Some(tcx.types.isize),
        "u8" => Some(tcx.types.u8),
        "u16" => Some(tcx.types.u16),
        "u32" => Some(tcx.types.u32),
        "u64" => Some(tcx.types.u64),
        "u128" => Some(tcx.types.u128),
        "usize" => Some(tcx.types.usize),
        "f16" => Some(tcx.types.f16),
        "f32" => Some(tcx.types.f32),
        "f64" => Some(tcx.types.f64),
        "f128" => Some(tcx.types.f128),
        "bool" => Some(tcx.types.bool),
        "char" => Some(tcx.types.char),
        "str" => Some(tcx.types.str_),
        _ => None,
    }
}

/// Find generic type parameters in the parameter list
fn find_generic_param(tcx: TyCtxt, def_id: DefId, type_ident: String) -> Option<Ty> {
    rap_debug!(
        "Searching for generic param: {} in {:?}",
        type_ident,
        def_id
    );
    let (_, param_tys) = parse_signature(tcx, def_id);
    rap_debug!("Function parameter types: {:?} of {:?}", param_tys, def_id);
    // 递归查找泛型参数
    for &ty in &param_tys {
        if let Some(found) = find_generic_in_ty(tcx, ty, &type_ident) {
            return Some(found);
        }
    }

    None
}

/// Iterate the args' types recursively and find the matched generic one.
fn find_generic_in_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, type_ident: &str) -> Option<Ty<'tcx>> {
    match ty.kind() {
        TyKind::Param(param_ty) => {
            if param_ty.name.as_str() == type_ident {
                return Some(ty);
            }
        }
        TyKind::RawPtr(ty, _)
        | TyKind::Ref(_, ty, _)
        | TyKind::Slice(ty)
        | TyKind::Array(ty, _) => {
            if let Some(found) = find_generic_in_ty(tcx, *ty, type_ident) {
                return Some(found);
            }
        }
        TyKind::Tuple(tys) => {
            for tuple_ty in tys.iter() {
                if let Some(found) = find_generic_in_ty(tcx, tuple_ty, type_ident) {
                    return Some(found);
                }
            }
        }
        TyKind::Adt(adt_def, substs) => {
            let name = tcx.item_name(adt_def.did()).to_string();
            if name == type_ident {
                return Some(ty);
            }
            for field in adt_def.all_fields() {
                let field_ty = field.ty(tcx, substs);
                if let Some(found) = find_generic_in_ty(tcx, field_ty, type_ident) {
                    return Some(found);
                }
            }
        }
        _ => {}
    }
    None
}

// /// Find user-defined types in the parameter list
// fn find_user_defined_type(tcx: TyCtxt, def_id: DefId, type_ident: String) -> Option<Ty> {
//     let param_ty = parse_signature(tcx, def_id).1;
//     param_ty.iter().find_map(|&ty| {
//         // Peel off references and pointers to get to the underlying type
//         let peeled_ty = ty.peel_refs();
//         match peeled_ty.kind() {
//             TyKind::Adt(adt_def, _raw_list) => {
//                 // Compare the type name to our identifier
//                 let name = tcx.item_name(adt_def.did()).to_string();
//                 if name == type_ident {
//                     return Some(peeled_ty);
//                 }
//             }
//             _ => {}
//         }
//         None
//     })
// }

pub fn reflect_generic<'tcx>(
    generic_mapping: &FxHashMap<String, Ty<'tcx>>,
    ty: Ty<'tcx>,
) -> Ty<'tcx> {
    match ty.kind() {
        TyKind::Param(param_ty) => {
            let generic_name = param_ty.name.to_string();
            if let Some(actual_ty) = generic_mapping.get(&generic_name) {
                return *actual_ty;
            }
        }
        _ => {}
    }
    ty
}

// fn find_first_chain_in_expr(expr: &Expr, param_names: &[String]) -> Option<(String, Vec<String>)> {
//     if let Some(chain) = access_ident_recursive(expr) {
//         if param_names.contains(&chain.0) {
//             return Some(chain);
//         }
//     }

//     let mut children = Vec::new();
//     match expr {
//         Expr::Array(expr) => children.extend(expr.elems.iter()),
//         Expr::Assign(expr) => {
//             children.push(&expr.left);
//             children.push(&expr.right);
//         }
//         Expr::Binary(expr) => {
//             children.push(&expr.left);
//             children.push(&expr.right);
//         }
//         Expr::Call(expr) => {
//             children.push(&expr.func);
//             children.extend(expr.args.iter());
//         }
//         Expr::Cast(expr) => children.push(&expr.expr),
//         Expr::Field(expr) => children.push(&expr.base),
//         Expr::Group(expr) => children.push(&expr.expr),
//         Expr::Index(expr) => {
//             children.push(&expr.expr);
//             children.push(&expr.index);
//         }
//         Expr::Let(expr) => children.push(&expr.expr),
//         // Expr::Lit(expr) => children.push(&expr.lit),
//         Expr::MethodCall(expr) => {
//             children.push(&expr.receiver);
//             children.extend(expr.args.iter());
//         }
//         Expr::Paren(expr) => children.push(&expr.expr),
//         Expr::Range(expr) => {
//             if let Some(start) = &expr.start {
//                 children.push(start);
//             }
//             if let Some(end) = &expr.end {
//                 children.push(end);
//             }
//             // if let Some(limits) = &expr.limits {
//             //     let _ = limits;
//             // }
//         }
//         Expr::Reference(expr) => children.push(&expr.expr),
//         Expr::Repeat(expr) => {
//             children.push(&expr.expr);
//             children.push(&expr.len);
//         }
//         // Expr::Struct(expr) => {
//         //     children.push(&expr.path);
//         //     for field in &expr.fields {
//         //         children.push(&field.expr);
//         //     }
//         //     if let Some(rest) = &expr.rest {
//         //         children.push(rest);
//         //     }
//         // }
//         Expr::Try(expr) => children.push(&expr.expr),
//         Expr::Tuple(expr) => children.extend(expr.elems.iter()),
//         Expr::Unary(expr) => children.push(&expr.expr),
//         _ => {}
//     }

//     for child in children {
//         if let Some(chain) = find_first_chain_in_expr(child, param_names) {
//             return Some(chain);
//         }
//     }

//     None
// }
