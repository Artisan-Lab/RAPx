use crate::analysis::utils::fn_info::*;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::def_id::CRATE_DEF_INDEX;
use rustc_middle::ty::Visibility;
use rustc_middle::{ty, ty::TyCtxt};
use std::collections::HashMap;
use std::collections::HashSet;
// use crate::analysis::unsafety_isolation::draw_dot::render_dot_graphs;

use super::{
    generate_dot::{NodeType, UigUnit},
    UnsafetyIsolationCheck,
};

impl<'tcx> UnsafetyIsolationCheck<'tcx> {
    pub fn handle_std_unsafe(&mut self) {
        self.get_all_std_unsafe_def_id_by_treat_std_as_local_crate(self.tcx);
        // self.get_units_data(self.tcx);
        let mut dot_strs = Vec::new();
        for uig in &self.uigs {
            let dot_str = uig.generate_dot_str();
            // uig.compare_labels(self.tcx);
            dot_strs.push(dot_str);
        }
        for uig in &self.single {
            let dot_str = uig.generate_dot_str();
            // uig.compare_labels(self.tcx);
            dot_strs.push(dot_str);
        }
        // println!("single {:?}",self.single.len());
        // render_dot_graphs(dot_strs);
    }

    pub fn get_all_std_unsafe_def_id_by_rustc_extern_crates(
        &mut self,
        tcx: TyCtxt<'tcx>,
    ) -> HashSet<DefId> {
        let mut visited = HashSet::new();
        let mut unsafe_fn = HashSet::new();
        for &crate_num in tcx.crates(()).iter() {
            let crate_name = tcx.crate_name(crate_num).to_string();
            // if crate_name == "std" || crate_name == "core" || crate_name == "alloc" {
            if crate_name == "core" {
                let crate_root = DefId {
                    krate: crate_num,
                    index: CRATE_DEF_INDEX,
                };
                self.process_def_id(tcx, crate_root, &mut visited, &mut unsafe_fn);
                println!(
                    "{:?} has {:?} MIR instances totally, with {:?} unsafe fns.",
                    crate_name,
                    visited.len(),
                    unsafe_fn.len()
                );
            }
        }
        // Self::print_hashset(&unsafe_fn);
        unsafe_fn
    }

    pub fn get_all_std_unsafe_def_id_by_treat_std_as_local_crate(
        &mut self,
        tcx: TyCtxt<'tcx>,
    ) -> HashSet<DefId> {
        let mut unsafe_fn = HashSet::new();
        let def_id_sets = tcx.mir_keys(());
        let mut sp_count_map: HashMap<String, usize> = HashMap::new();

        for local_def_id in def_id_sets {
            let def_id = local_def_id.to_def_id();
            if Self::filter_mir(def_id) {
                continue;
            }
            if tcx.def_kind(def_id) == DefKind::Fn || tcx.def_kind(def_id) == DefKind::AssocFn {
                // if Self::check_safety(tcx, def_id)
                //     && Self::check_visibility(tcx, def_id)
                if check_visibility(tcx, def_id) {
                    if check_safety(tcx, def_id) {
                        let sp_set = get_sp(tcx, def_id);
                        if sp_set.len() != 0 {
                            unsafe_fn.insert(def_id);
                            // println!("unsafe fn : {:?}", UigUnit::get_cleaned_def_path_name(self.tcx, def_id));
                        }
                        for sp in sp_set {
                            *sp_count_map.entry(sp).or_insert(0) += 1;
                        }
                    }
                    self.insert_uig(def_id, get_callees(tcx, def_id), get_cons(tcx, def_id));
                }
            }
        }
        self.analyze_struct();
        // self.analyze_uig();
        // for (sp, count) in &sp_count_map {
        //     println!("SP: {}, Count: {}", sp, count);
        // }
        // println!("uig and single len : {:?} and {:?}", self.uigs.len(), self.single.len());
        // println!("unsafe fn len {}", unsafe_fn.len());
        unsafe_fn
    }

    pub fn analyze_uig(&self) {
        let mut pro1 = Vec::new();
        let mut enc1 = Vec::new();
        for uig in &self.uigs {
            if uig.caller.1 != true && uig.caller.2 == 2 {
                enc1.push(uig.clone());
            } else if uig.caller.1 == true && uig.caller.2 == 2 {
                pro1.push(uig.clone());
            }
        }

        let mut no_unsafe_con = Vec::new();
        for uig in pro1 {
            let mut flag = 0;
            for con in &uig.caller_cons {
                if con.1 == true {
                    flag = 1;
                }
            }
            if flag == 0 {
                no_unsafe_con.push(uig.clone());
            }
        }
    }

    pub fn analyze_struct(&self) {
        let mut cache = HashSet::new();
        for uig in &self.uigs {
            self.get_struct(uig.caller.0, &mut cache);
        }
        for uig in &self.single {
            self.get_struct(uig.caller.0, &mut cache);
        }
    }

    pub fn get_struct(&self, def_id: DefId, cache: &mut HashSet<DefId>) {
        let tcx = self.tcx;
        let mut safe_constructors = Vec::new();
        let mut unsafe_constructors = Vec::new();
        let mut unsafe_methods = Vec::new();
        let mut safe_methods = Vec::new();
        let mut mut_methods = Vec::new();
        let mut struct_name = "".to_string();
        let mut ty_flag = 0;
        if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
            if let Some(impl_id) = assoc_item.impl_container(tcx) {
                // get struct ty
                let ty = tcx.type_of(impl_id).skip_binder();
                if let Some(adt_def) = ty.ty_adt_def() {
                    if adt_def.is_union() {
                        ty_flag = 1;
                    } else if adt_def.is_enum() {
                        ty_flag = 2;
                    }
                    let adt_def_id = adt_def.did();
                    struct_name = get_cleaned_def_path_name(tcx, adt_def_id);
                    if !cache.insert(adt_def_id) {
                        return;
                    }
                    if !check_visibility(self.tcx, adt_def_id) {
                        return;
                    }
                    let impl_vec = get_impls_for_struct(self.tcx, adt_def_id);
                    for impl_id in impl_vec {
                        let associated_items = tcx.associated_items(impl_id);
                        for item in associated_items.in_definition_order() {
                            if let ty::AssocKind::Fn = item.kind {
                                let item_def_id = item.def_id;
                                if !check_visibility(self.tcx, item_def_id) {
                                    continue;
                                }
                                if get_type(self.tcx, item_def_id) == 0
                                    && check_safety(self.tcx, item_def_id) == true
                                {
                                    unsafe_constructors.push(item_def_id);
                                }
                                if get_type(self.tcx, item_def_id) == 0
                                    && check_safety(self.tcx, item_def_id) == false
                                {
                                    safe_constructors.push(item_def_id);
                                }
                                if get_type(self.tcx, item_def_id) == 1
                                    && check_safety(self.tcx, item_def_id) == true
                                {
                                    unsafe_methods.push(item_def_id);
                                }
                                if get_type(self.tcx, item_def_id) == 1
                                    && check_safety(self.tcx, item_def_id) == false
                                {
                                    if get_callees(tcx, item_def_id).len() != 0 {
                                        safe_methods.push(item_def_id);
                                    }
                                }
                                if get_type(self.tcx, item_def_id) == 1
                                    && has_mut_self_param(self.tcx, item_def_id) == true
                                {
                                    mut_methods.push(item_def_id);
                                }
                            }
                        }
                    }
                }
            }
        }
        if struct_name == "".to_string()
            || (unsafe_constructors.len() == 0
                && unsafe_methods.len() == 0
                && safe_methods.len() == 0)
        {
            return;
        }
        if ty_flag == 0 {
            println!("Struct:{:?}", struct_name);
        }
        if ty_flag == 1 {
            println!("Union:{:?}", struct_name);
        }
        if ty_flag == 2 {
            println!("Enum:{:?}", struct_name);
        }
        println!("Safe Cons: {}", safe_constructors.len());
        // for safe_cons in safe_constructors {
        //     println!(" {:?}", get_cleaned_def_path_name(tcx, safe_cons));
        // }
        println!("Unsafe Cons: {}", unsafe_constructors.len());
        // for unsafe_cons in unsafe_constructors {
        //     println!(" {:?}", get_cleaned_def_path_name(tcx, unsafe_cons));
        // }
        println!("Unsafe Methods: {}", unsafe_methods.len());
        // for method in unsafe_methods {
        //     println!(" {:?}", get_cleaned_def_path_name(tcx, method));
        // }
        println!("Safe Methods with unsafe callee: {}", safe_methods.len());
        // for method in safe_methods {
        //     println!(" {:?}", get_cleaned_def_path_name(tcx, method));
        // }
        println!("Mut self Methods: {}", mut_methods.len());
        // for method in mut_methods {
        //     println!(" {:?}", get_cleaned_def_path_name(tcx, method));
        // }
    }

    pub fn get_units_data(&mut self, tcx: TyCtxt<'tcx>) {
        // [uf/um, sf-uf, sf-um, uf-uf, uf-um, um(sf)-uf, um(uf)-uf, um(sf)-um, um(uf)-um, sm(sf)-uf, sm(uf)-uf, sm(sf)-um, sm(uf)-um]
        let mut basic_units_data = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        let def_id_sets = tcx.mir_keys(());
        for local_def_id in def_id_sets {
            let def_id = local_def_id.to_def_id();
            if Self::filter_mir(def_id) {
                continue;
            }
            if tcx.def_kind(def_id) == DefKind::Fn || tcx.def_kind(def_id) == DefKind::AssocFn {
                if check_visibility(tcx, def_id) {
                    self.insert_uig(def_id, get_callees(tcx, def_id), get_cons(tcx, def_id));
                }
            }
        }
        for uig in &self.uigs {
            uig.count_basic_units(&mut basic_units_data);
        }
        for single in &self.single {
            single.count_basic_units(&mut basic_units_data);
        }
        println!("basic_units_data : {:?}", basic_units_data);
    }

    pub fn process_def_id(
        &mut self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        visited: &mut HashSet<DefId>,
        unsafe_fn: &mut HashSet<DefId>,
    ) {
        if !visited.insert(def_id) || Self::filter_mir(def_id) {
            return;
        }
        match tcx.def_kind(def_id) {
            DefKind::Fn | DefKind::AssocFn => {
                if check_safety(tcx, def_id) && self.tcx.visibility(def_id) == Visibility::Public {
                    unsafe_fn.insert(def_id);
                    self.insert_uig(def_id, get_callees(tcx, def_id), get_cons(tcx, def_id));
                }
            }
            DefKind::Mod => {
                for child in tcx.module_children(def_id) {
                    if let Some(child_def_id) = child.res.opt_def_id() {
                        self.process_def_id(tcx, child_def_id, visited, unsafe_fn);
                    }
                }
            }
            DefKind::Impl { of_trait: _ } => {
                for item in tcx.associated_item_def_ids(def_id) {
                    self.process_def_id(tcx, *item, visited, unsafe_fn);
                }
            }
            DefKind::Struct => {
                let impls = tcx.inherent_impls(def_id);
                for impl_def_id in impls {
                    self.process_def_id(tcx, *impl_def_id, visited, unsafe_fn);
                }
            }
            DefKind::Ctor(_of, _kind) => {
                if tcx.is_mir_available(def_id) {
                    let _mir = tcx.optimized_mir(def_id);
                }
            }
            _ => {
                // println!("{:?}",tcx.def_kind(def_id));
            }
        }
    }

    pub fn filter_mir(def_id: DefId) -> bool {
        let def_id_fmt = format!("{:?}", def_id);
        def_id_fmt.contains("core_arch")
            || def_id_fmt.contains("::__")
            || def_id_fmt.contains("backtrace_rs")
            || def_id_fmt.contains("stack_overflow")
            || def_id_fmt.contains("thread_local")
            || def_id_fmt.contains("raw_vec")
            || def_id_fmt.contains("sys_common")
            || def_id_fmt.contains("adapters")
            || def_id_fmt.contains("sys::sync")
            || def_id_fmt.contains("personality")
            || def_id_fmt.contains("collections::btree::borrow")
            || def_id_fmt.contains("num::int_sqrt")
            || def_id_fmt.contains("collections::btree::node")
            || def_id_fmt.contains("collections::btree::navigate")
            || def_id_fmt.contains("core_simd")
            || def_id_fmt.contains("unique")
    }

    pub fn insert_uig(
        &mut self,
        caller: DefId,
        callee_set: HashSet<DefId>,
        caller_cons: Vec<NodeType>,
    ) {
        let mut pairs = HashSet::new();
        for callee in &callee_set {
            let callee_cons = get_cons(self.tcx, *callee);
            pairs.insert((generate_node_ty(self.tcx, *callee), callee_cons));
        }
        if !check_safety(self.tcx, caller) && callee_set.len() == 0 {
            return;
        }
        let uig = UigUnit::new_by_pair(generate_node_ty(self.tcx, caller), caller_cons, pairs);
        if callee_set.len() > 0 {
            self.uigs.push(uig);
        } else {
            self.single.push(uig);
        }
    }
}
