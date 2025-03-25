use crate::analysis::senryx::matcher::parse_unsafe_api;
use crate::analysis::unsafety_isolation::generate_dot::NodeType;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Terminator};
use rustc_middle::ty::Ty;
use rustc_middle::ty::TyCtxt;
use rustc_middle::{
    mir::{Operand, TerminatorKind},
    ty,
};
use rustc_span::def_id::LocalDefId;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;

pub fn generate_node_ty(tcx: TyCtxt<'_>, def_id: DefId) -> NodeType {
    (def_id, check_safety(tcx, def_id), get_type(tcx, def_id))
}

pub fn check_visibility(tcx: TyCtxt<'_>, func_defid: DefId) -> bool {
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

pub fn is_re_exported(tcx: TyCtxt<'_>, target_defid: DefId, module_defid: LocalDefId) -> bool {
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

pub fn get_cleaned_def_path_name(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    let def_id_str = format!("{:?}", def_id);
    let mut parts: Vec<&str> = def_id_str
        .split("::")
        // .filter(|part| !part.contains("{")) // 去除包含 "{" 的部分
        .collect();

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
                    match get_struct_name(tcx, def_id) {
                        Some(name) => Some(name),
                        None => None,
                    }
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
        if assoc_item.fn_has_self_parameter {
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
        }
    }
    return node_type;
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
                            && check_visibility(tcx, *item)
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
            match &bb.terminator().kind {
                TerminatorKind::Call { func, .. } => {
                    if let Operand::Constant(func_constant) = func {
                        if let ty::FnDef(ref callee_def_id, _) = func_constant.const_.ty().kind() {
                            if check_safety(tcx, *callee_def_id)
                                && check_visibility(tcx, *callee_def_id)
                            {
                                let sp_set = get_sp(tcx, *callee_def_id);
                                if sp_set.len() != 0 {
                                    callees.insert(*callee_def_id);
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
    return callees;
}

pub fn get_impls_for_struct(tcx: TyCtxt<'_>, struct_def_id: DefId) -> Vec<DefId> {
    let mut impls = Vec::new();
    for item_id in tcx.hir().items() {
        let item = tcx.hir().item(item_id);
        if let rustc_hir::ItemKind::Impl(ref impl_item) = item.kind {
            if let rustc_hir::TyKind::Path(ref qpath) = impl_item.self_ty.kind {
                if let rustc_hir::QPath::Resolved(_, ref path) = qpath {
                    if let rustc_hir::def::Res::Def(_, ref def_id) = path.res {
                        if *def_id == struct_def_id {
                            impls.push(item.owner_id.to_def_id());
                        }
                    }
                }
            }
        }
    }
    impls
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
    get_pointee(matched_ty) != matched_ty
}

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

pub fn get_all_std_unsafe_callees(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<String> {
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

pub fn match_std_unsafe_callee(tcx: TyCtxt<'_>, terminator: &Terminator<'_>) -> Vec<String> {
    let mut results = Vec::new();
    match &terminator.kind {
        TerminatorKind::Call { func, .. } => {
            if let Operand::Constant(func_constant) = func {
                if let ty::FnDef(ref callee_def_id, _raw_list) = func_constant.const_.ty().kind() {
                    let func_name = get_cleaned_def_path_name(tcx, *callee_def_id);
                    if parse_unsafe_api(&func_name).is_some() {
                        results.push(func_name);
                    }
                }
            }
        }
        _ => {}
    }
    results
}
