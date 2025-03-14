pub mod draw_dot;
pub mod generate_dot;
pub mod hir_visitor;
pub mod isolation_graph;
pub mod std_unsafety_isolation;

// use crate::analysis::unsafety_isolation::draw_dot::render_dot_graphs;
use crate::analysis::unsafety_isolation::generate_dot::UigUnit;
use crate::analysis::unsafety_isolation::hir_visitor::{ContainsUnsafe, RelatedFnCollector};
use crate::analysis::unsafety_isolation::isolation_graph::*;
use crate::analysis::utils::fn_info::*;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Operand, TerminatorKind},
    ty,
    ty::TyCtxt,
};
use std::collections::VecDeque;

#[derive(PartialEq)]
pub enum UigInstruction {
    Doc,
    Upg,
    Ucons,
    StdSp,
}

pub struct UnsafetyIsolationCheck<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub nodes: Vec<IsolationGraphNode>,
    pub related_func_def_id: Vec<DefId>,
    pub uigs: Vec<UigUnit>,
    pub single: Vec<UigUnit>,
}

impl<'tcx> UnsafetyIsolationCheck<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            nodes: Vec::new(),
            related_func_def_id: Vec::new(),
            uigs: Vec::new(),
            single: Vec::new(),
        }
    }

    pub fn start(&mut self, ins: UigInstruction) {
        if ins == UigInstruction::StdSp {
            self.handle_std_unsafe();
            return;
        } else if ins == UigInstruction::Upg {
            return; //TODO:
        }
        let related_items = RelatedFnCollector::collect(self.tcx);
        let hir_map = self.tcx.hir();
        let mut ufunc = 0;
        for (_, &ref vec) in &related_items {
            for (body_id, span) in vec {
                let (function_unsafe, _block_unsafe) =
                    ContainsUnsafe::contains_unsafe(self.tcx, *body_id);
                let def_id = hir_map.body_owner_def_id(*body_id).to_def_id();
                if function_unsafe {
                    ufunc = ufunc + 1;
                    if ins == UigInstruction::Doc {
                        self.check_doc(def_id);
                    }
                    if ins == UigInstruction::Ucons {
                        if get_type(self.tcx, def_id) == 0 {
                            println!(
                                "Find unsafe constructor: {:?}, location:{:?}.",
                                def_id, span
                            );
                        }
                    }
                }
            }
        }
    }

    pub fn check_doc(&self, def_id: DefId) {
        if !self.check_if_unsafety_doc_exists(def_id) {
            let visibility = self.tcx.visibility(def_id);
            println!(
                "Lack of unsafety doc: {:?}, visibility:{:?}.",
                self.tcx.def_span(def_id),
                visibility
            );
        }
    }

    pub fn filter_and_extend_unsafe(&mut self) {
        let related_items = RelatedFnCollector::collect(self.tcx);
        let hir_map = self.tcx.hir();
        let mut queue = VecDeque::new();
        let mut visited = std::collections::HashSet::new();

        //'related_items' is used for recording whether this api is in crate or not
        //then init the queue, including all unsafe func and interior unsafe func
        for (_, &ref vec) in &related_items {
            for (body_id, _) in vec {
                let (function_unsafe, block_unsafe) =
                    ContainsUnsafe::contains_unsafe(self.tcx, *body_id);
                let body_did = hir_map.body_owner_def_id(*body_id).to_def_id();
                if function_unsafe || block_unsafe {
                    let node_type = get_type(self.tcx, body_did);
                    let name = self.get_name(body_did);
                    let mut new_node =
                        IsolationGraphNode::new(body_did, node_type, name, function_unsafe, true);
                    if node_type == 1 {
                        new_node.constructors = self.search_constructor(body_did);
                    }
                    self.nodes.push(new_node);
                    self.related_func_def_id.push(body_did);
                    if visited.insert(body_did) {
                        queue.push_back(body_did);
                    }
                }
            }
        }

        // BFS handling the queue
        while let Some(body_did) = queue.pop_front() {
            if !self.is_crate_api_node(body_did) {
                continue;
            }
            // get all unsafe callees in current crate api and insert to queue
            let callees = self.visit_node_callees(body_did);
            for &callee_id in &callees {
                if visited.insert(callee_id) {
                    queue.push_back(callee_id);
                }
            }
        }
    }

    fn check_if_unsafety_doc_exists(&self, def_id: DefId) -> bool {
        if def_id.krate == rustc_hir::def_id::LOCAL_CRATE {
            let attrs = self.tcx.get_attrs_unchecked(def_id);
            for attr in attrs {
                if attr.is_doc_comment() {
                    return true;
                }
            }
        }
        return false;
    }

    pub fn check_if_node_exists(&self, body_did: DefId) -> bool {
        if let Some(_node) = self.nodes.iter().find(|n| n.node_id == body_did) {
            return true;
        }
        return false;
    }

    pub fn get_name(&self, body_did: DefId) -> String {
        let tcx = self.tcx;
        let mut name = String::new();
        if let Some(assoc_item) = tcx.opt_associated_item(body_did) {
            if let Some(impl_id) = assoc_item.impl_container(tcx) {
                // get struct name
                let ty = tcx.type_of(impl_id).skip_binder();
                let type_name = ty.to_string();
                let type_name = type_name.split('<').next().unwrap_or("").trim();
                // get method name
                let method_name = tcx.def_path(body_did).to_string_no_crate_verbose();
                let method_name = method_name.split("::").last().unwrap_or("");
                name = format!("{}.{}", type_name, method_name);
            }
        } else {
            let verbose_name = tcx.def_path(body_did).to_string_no_crate_verbose();
            name = verbose_name.split("::").last().unwrap_or("").to_string();
        }
        return name;
    }

    pub fn search_constructor(&mut self, def_id: DefId) -> Vec<DefId> {
        let tcx = self.tcx;
        let mut constructors = Vec::new();
        if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
            if let Some(impl_id) = assoc_item.impl_container(tcx) {
                // get struct ty
                let ty = tcx.type_of(impl_id).skip_binder();
                if let Some(adt_def) = ty.ty_adt_def() {
                    let adt_def_id = adt_def.did();
                    let impl_vec = get_impls_for_struct(self.tcx, adt_def_id);
                    for impl_id in impl_vec {
                        let associated_items = tcx.associated_items(impl_id);
                        for item in associated_items.in_definition_order() {
                            if let ty::AssocKind::Fn = item.kind {
                                let item_def_id = item.def_id;
                                if get_type(self.tcx, item_def_id) == 0 {
                                    constructors.push(item_def_id);
                                    self.check_and_insert_node(item_def_id);
                                    self.set_method_for_constructor(item_def_id, def_id);
                                }
                            }
                        }
                    }
                }
            }
        }
        constructors
    }

    pub fn get_cons_counts(&self, def_id: DefId) -> Vec<DefId> {
        let tcx = self.tcx;
        let mut constructors = Vec::new();
        let mut methods = Vec::new();
        if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
            if let Some(impl_id) = assoc_item.impl_container(tcx) {
                // get struct ty
                let ty = tcx.type_of(impl_id).skip_binder();
                if let Some(adt_def) = ty.ty_adt_def() {
                    let adt_def_id = adt_def.did();
                    let impl_vec = get_impls_for_struct(self.tcx, adt_def_id);
                    for impl_id in impl_vec {
                        let associated_items = tcx.associated_items(impl_id);
                        for item in associated_items.in_definition_order() {
                            if let ty::AssocKind::Fn = item.kind {
                                let item_def_id = item.def_id;
                                if get_type(self.tcx, item_def_id) == 0 {
                                    constructors.push(item_def_id);
                                } else if get_type(self.tcx, item_def_id) == 1 {
                                    methods.push(item_def_id);
                                }
                            }
                        }
                    }
                }
                print!("struct:{:?}", ty);
            }
        }
        println!("--------methods:{:?}", methods.len());
        constructors
    }

    // visit the func body and record all its unsafe callees and modify visited_tag
    pub fn visit_node_callees(&mut self, def_id: DefId) -> Vec<DefId> {
        let mut callees = Vec::new();
        let tcx = self.tcx;
        if tcx.is_mir_available(def_id) {
            let body = tcx.optimized_mir(def_id);
            for bb in body.basic_blocks.iter() {
                match &bb.terminator().kind {
                    TerminatorKind::Call { func, .. } => {
                        if let Operand::Constant(func_constant) = func {
                            if let ty::FnDef(ref callee_def_id, _) =
                                func_constant.const_.ty().kind()
                            {
                                if check_safety(self.tcx, *callee_def_id) {
                                    if !callees.contains(callee_def_id) {
                                        callees.push(*callee_def_id);
                                        if !self.check_if_node_exists(*callee_def_id) {
                                            self.check_and_insert_node(*callee_def_id);
                                            self.set_caller_for_callee(def_id, *callee_def_id);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        if let Some(node) = self.nodes.iter_mut().find(|n| n.node_id == def_id) {
            node.callees = callees.clone();
            node.visited_tag = true;
        }
        return callees;
    }

    pub fn is_crate_api_node(&self, body_did: DefId) -> bool {
        return self.related_func_def_id.contains(&body_did);
    }

    pub fn check_and_insert_node(&mut self, body_did: DefId) {
        if self.check_if_node_exists(body_did) {
            return;
        }
        let node_type = get_type(self.tcx, body_did);
        let name = self.get_name(body_did);
        let is_crate_api = self.is_crate_api_node(body_did);
        let node_safety = check_safety(self.tcx, body_did);
        let mut new_node =
            IsolationGraphNode::new(body_did, node_type, name, node_safety, is_crate_api);
        if node_type == 1 {
            new_node.constructors = self.search_constructor(body_did);
        }
        new_node.visited_tag = false;
        self.nodes.push(new_node);
    }

    pub fn set_method_for_constructor(&mut self, constructor_did: DefId, method_did: DefId) {
        if let Some(node) = self
            .nodes
            .iter_mut()
            .find(|node| node.node_id == constructor_did)
        {
            if !node.methods.contains(&method_did) {
                node.methods.push(method_did);
            }
        }
    }

    pub fn set_caller_for_callee(&mut self, caller_did: DefId, callee_did: DefId) {
        if let Some(node) = self
            .nodes
            .iter_mut()
            .find(|node| node.node_id == callee_did)
        {
            if !node.callers.contains(&caller_did) {
                node.callers.push(caller_did);
            }
        }
    }

    pub fn show_nodes(&self) {
        for node in &self.nodes {
            println!(
                "name:{:?},safety:{:?},calles:{:?}",
                node.node_name, node.node_unsafety, node.callees
            );
        }
    }
}
