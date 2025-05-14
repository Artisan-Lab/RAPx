use crate::analysis::utils::fn_info::*;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::Visibility;
use rustc_middle::{ty, ty::TyCtxt};
use std::collections::HashMap;
use std::collections::HashSet;
// use crate::analysis::unsafety_isolation::draw_dot::render_dot_graphs;
use super::{
    generate_dot::{NodeType, UigUnit},
    UnsafetyIsolationCheck,
};
use rustc_middle::mir::Local;

impl<'tcx> UnsafetyIsolationCheck<'tcx> {
    pub fn handle_std_unsafe(&mut self) {
        self.get_all_std_unsafe_def_id_by_treat_std_as_local_crate(self.tcx);
        // self.get_units_data(self.tcx);
        let mut dot_strs = Vec::new();
        for uig in &self.uigs {
            let dot_str = uig.generate_dot_str();
            dot_strs.push(dot_str);
        }
        for uig in &self.single {
            let dot_str = uig.generate_dot_str();
            dot_strs.push(dot_str);
            // println!("{:?}", get_cleaned_def_path_name(self.tcx, uig.caller.0));
        }
        // println!("single {:?}",self.uigs.len());
        // println!("single {:?}",self.single.len());
        // render_dot_graphs(dot_strs);
    }

    pub fn get_all_std_unsafe_def_id_by_treat_std_as_local_crate(
        &mut self,
        tcx: TyCtxt<'tcx>,
    ) -> HashSet<DefId> {
        let mut unsafe_fn = HashSet::new();
        let mut total_cnt = 0;
        let mut api_cnt = 0;
        let mut sp_cnt = 0;
        let def_id_sets = tcx.mir_keys(());
        let mut sp_count_map: HashMap<String, usize> = HashMap::new();

        for local_def_id in def_id_sets {
            let def_id = local_def_id.to_def_id();
            if Self::filter_mir(def_id) {
                continue;
            }
            if get_cleaned_def_path_name(self.tcx, def_id).contains("UdpSocket") {
                println!("1");
                let impl_vec = get_impls_for_struct(self.tcx, def_id);
                for impl_id in impl_vec {
                    println!("2");

                    let associated_items = tcx.associated_items(impl_id);
                    for item in associated_items.in_definition_order() {
                        if let ty::AssocKind::Fn = item.kind {
                            let item_def_id = item.def_id;
                            println!("method {:?}", item_def_id);
                        }
                    }
                }
            }
            if tcx.def_kind(def_id) == DefKind::Fn || tcx.def_kind(def_id) == DefKind::AssocFn {
                if check_safety(tcx, def_id)
                    && !get_cleaned_def_path_name(self.tcx, def_id).contains("intrinsic")
                {
                    // if get_cleaned_def_path_name(self.tcx, def_id).contains("std::") {
                    //     println!("{:?}", get_cleaned_def_path_name(self.tcx, def_id));
                    // }
                    let sp_set = get_sp(tcx, def_id);
                    if sp_set.len() != 0 {
                        unsafe_fn.insert(def_id);
                        let mut flag = false;
                        for sp in &sp_set {
                            if sp == ""
                                || sp == "Function_sp"
                                || sp == "System_sp"
                                || sp == "ValidSlice"
                            {
                                flag = true;
                            }
                        }
                        if flag == false {
                            api_cnt += 1;
                            sp_cnt += sp_set.len();
                        }
                        total_cnt += 1;
                        // println!("unsafe fn : {:?}", get_cleaned_def_path_name(self.tcx, def_id));
                    }
                    for sp in sp_set {
                        *sp_count_map.entry(sp).or_insert(0) += 1;
                    }
                    // self.check_params(def_id);
                }
                self.insert_uig(def_id, get_callees(tcx, def_id), get_cons(tcx, def_id));
            }
        }
        self.analyze_struct();
        // self.analyze_uig();
        // self.get_units_data(self.tcx);
        // for (sp, count) in &sp_count_map {
        //     println!("SP: {}, Count: {}", sp, count);
        // }
        println!(
            "count : {:?} and {:?}, sp cnt : {}",
            total_cnt, api_cnt, sp_cnt
        );
        // println!("unsafe fn len {}", unsafe_fn.len());
        unsafe_fn
    }

    pub fn check_params(&self, def_id: DefId) {
        let body = self.tcx.optimized_mir(def_id);
        let locals = body.local_decls.clone();
        let fn_sig = self.tcx.fn_sig(def_id).skip_binder();
        let param_len = fn_sig.inputs().skip_binder().len();
        let return_ty = fn_sig.output().skip_binder();
        for idx in 1..param_len + 1 {
            let local_ty = locals[Local::from(idx)].ty;
            if is_ptr(local_ty) && !return_ty.is_unit() {
                println!("{:?}", get_cleaned_def_path_name(self.tcx, def_id));
            }
        }
    }

    pub fn analyze_uig(&self) {
        let mut func_nc = Vec::new();
        let mut func_pro1 = Vec::new();
        let mut func_enc1 = Vec::new();
        let mut m_nc = Vec::new();
        let mut m_pro1 = Vec::new();
        let mut m_enc1 = Vec::new();
        for uig in &self.uigs {
            if uig.caller.2 == 1 {
                // method
                if uig.caller.1 == true {
                    m_pro1.push(uig.clone());
                } else if uig.caller.1 != true {
                    m_enc1.push(uig.clone());
                }
            } else {
                //function
                if uig.caller.1 == true {
                    func_pro1.push(uig.clone());
                } else if uig.caller.1 != true {
                    func_enc1.push(uig.clone());
                }
            }
        }
        for uig in &self.single {
            if uig.caller.2 == 1 {
                // method
                m_nc.push(uig.clone());
            } else {
                func_nc.push(uig.clone());
            }
        }
        println!(
            "func: {},{},{}, method: {},{},{}",
            func_nc.len(),
            func_pro1.len(),
            func_enc1.len(),
            m_nc.len(),
            m_pro1.len(),
            m_enc1.len()
        );
        println!("units: {}", self.uigs.len() + self.single.len());
        // let mut no_unsafe_con = Vec::new();
        // for uig in pro1 {
        //     let mut flag = 0;
        //     for con in &uig.caller_cons {
        //         if con.1 == true {
        //             flag = 1;
        //         }
        //     }
        //     if flag == 0 {
        //         no_unsafe_con.push(uig.clone());
        //     }
        // }
    }

    pub fn analyze_struct(&self) {
        let mut cache = HashSet::new();
        let mut s = 0;
        let mut u = 0;
        let mut e = 0;
        let mut uc = 0;
        let mut vi = 0;
        for uig in &self.uigs {
            self.get_struct(
                uig.caller.0,
                &mut cache,
                &mut s,
                &mut u,
                &mut e,
                &mut uc,
                &mut vi,
            );
        }
        for uig in &self.single {
            self.get_struct(
                uig.caller.0,
                &mut cache,
                &mut s,
                &mut u,
                &mut e,
                &mut uc,
                &mut vi,
            );
        }
        println!("{},{},{},{}", s, u, e, vi);
    }

    pub fn get_struct(
        &self,
        def_id: DefId,
        cache: &mut HashSet<DefId>,
        s: &mut usize,
        u: &mut usize,
        e: &mut usize,
        uc: &mut usize,
        vi: &mut usize,
    ) {
        let tcx = self.tcx;
        let mut safe_constructors = Vec::new();
        let mut unsafe_constructors = Vec::new();
        let mut unsafe_methods = Vec::new();
        let mut safe_methods = Vec::new();
        let mut mut_methods = Vec::new();
        let mut struct_name = "".to_string();
        let mut ty_flag = 0;
        let mut vi_flag = false;
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

                    vi_flag = false;
                    let impl_vec = get_impls_for_struct(self.tcx, adt_def_id);
                    for impl_id in impl_vec {
                        let associated_items = tcx.associated_items(impl_id);
                        for item in associated_items.in_definition_order() {
                            if let ty::AssocKind::Fn = item.kind {
                                let item_def_id = item.def_id;
                                if get_sp(self.tcx, item_def_id).len() > 0 {
                                    vi_flag = true;
                                }
                                if get_type(self.tcx, item_def_id) == 0
                                    && check_safety(self.tcx, item_def_id) == true
                                // && get_sp(self.tcx, item_def_id).len() > 0
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
                                // && get_sp(self.tcx, item_def_id).len() > 0
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
        if vi_flag {
            *vi += 1;
        }
        if unsafe_constructors.len() > 0 {
            *uc += 1;
        }
        if ty_flag == 0 {
            *s += 1;
            // println!("Struct:{:?}", struct_name);
        }
        if ty_flag == 1 {
            *u += 1;
            // println!("Union:{:?}", struct_name);
        }
        if ty_flag == 2 {
            *e += 1;
            // println!("Enum:{:?}", struct_name);
        }

        // println!("Safe Cons: {}", safe_constructors.len());
        // for safe_cons in safe_constructors {
        //     println!(" {:?}", get_cleaned_def_path_name(tcx, safe_cons));
        // }
        // println!("Unsafe Cons: {}", unsafe_constructors.len());
        // for unsafe_cons in unsafe_constructors {
        //     println!(" {:?}", get_cleaned_def_path_name(tcx, unsafe_cons));
        // }
        // println!("Unsafe Methods: {}", unsafe_methods.len());
        // for method in unsafe_methods {
        //     println!(" {:?}", get_cleaned_def_path_name(tcx, method));
        // }
        // println!("Safe Methods with unsafe callee: {}", safe_methods.len());
        // for method in safe_methods {
        //     println!(" {:?}", get_cleaned_def_path_name(tcx, method));
        // }
        // println!("Mut self Methods: {}", mut_methods.len());
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
                self.insert_uig(def_id, get_callees(tcx, def_id), get_cons(tcx, def_id));
            }
        }
        for uig in &self.uigs {
            uig.count_basic_units(&mut basic_units_data);
        }
        for single in &self.single {
            single.count_basic_units(&mut basic_units_data);
        }
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

    pub fn filter_mir(_def_id: DefId) -> bool {
        // let def_id_fmt = format!("{:?}", def_id);
        return false;
        // def_id_fmt.contains("core_arch")
        //     || def_id_fmt.contains("::__")
        //     || def_id_fmt.contains("backtrace_rs")
        //     || def_id_fmt.contains("stack_overflow")
        //     || def_id_fmt.contains("thread_local")
        //     || def_id_fmt.contains("raw_vec")
        //     || def_id_fmt.contains("sys_common")
        //     || def_id_fmt.contains("adapters")
        //     || def_id_fmt.contains("sys::sync")
        //     || def_id_fmt.contains("personality")
        //     || def_id_fmt.contains("collections::btree::borrow")
        //     || def_id_fmt.contains("num::int_sqrt")
        //     || def_id_fmt.contains("collections::btree::node")
        //     || def_id_fmt.contains("collections::btree::navigate")
        //     || def_id_fmt.contains("core_simd")
        //     || def_id_fmt.contains("unique")
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
        // if check_safety(self.tcx, caller)
        // && get_sp(self.tcx, caller).len() == 0
        // {
        //     println!("{:?}",get_cleaned_def_path_name(self.tcx, caller));
        //     return;
        // }
        let uig = UigUnit::new_by_pair(generate_node_ty(self.tcx, caller), caller_cons, pairs);
        if callee_set.len() > 0 {
            self.uigs.push(uig);
        } else {
            self.single.push(uig);
        }
    }
}
