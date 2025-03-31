use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt};
use std::collections::{HashMap, HashSet, VecDeque};

use crate::analysis::utils::fn_info::{get_pointee, is_ptr, is_ref};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct States {
    pub nonnull: bool,
    pub allocator_consistency: bool,
}

impl States {
    pub fn new() -> Self {
        Self {
            nonnull: true,
            allocator_consistency: true,
        }
    }

    pub fn new_unknown() -> Self {
        Self {
            nonnull: false,
            allocator_consistency: false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct VariableNode<'tcx> {
    pub id: usize,
    points_to: Option<usize>,
    pointed_by: HashSet<usize>,
    pub field: HashMap<usize, usize>,
    pub ty: Ty<'tcx>,
    pub is_dropped: bool,
    pub states: States,
}

impl<'tcx> VariableNode<'tcx> {
    pub fn new(
        id: usize,
        points_to: Option<usize>,
        pointed_by: HashSet<usize>,
        ty: Ty<'tcx>,
        states: States,
    ) -> Self {
        VariableNode {
            id,
            points_to,
            pointed_by,
            field: HashMap::new(),
            ty,
            is_dropped: false,
            states,
        }
    }

    pub fn new_default(id: usize, ty: Ty<'tcx>) -> Self {
        VariableNode {
            id,
            points_to: None,
            pointed_by: HashSet::new(),
            field: HashMap::new(),
            ty,
            is_dropped: false,
            states: States::new(),
        }
    }

    pub fn new_with_states(id: usize, ty: Ty<'tcx>, states: States) -> Self {
        VariableNode {
            id,
            points_to: None,
            pointed_by: HashSet::new(),
            field: HashMap::new(),
            ty,
            is_dropped: false,
            states,
        }
    }
}

pub struct DominatedGraph<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub def_id: DefId,
    local_len: usize,
    pub variables: HashMap<usize, VariableNode<'tcx>>,
}

impl<'tcx> DominatedGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        let body = tcx.optimized_mir(def_id);
        let locals = body.local_decls.clone();
        let fn_sig = tcx.fn_sig(def_id).skip_binder();
        let param_len = fn_sig.inputs().skip_binder().len();
        let mut var_map = HashMap::new();
        let mut obj_cnt = 0;
        for (idx, local) in locals.iter().enumerate() {
            let local_ty = local.ty;
            // Init the pointed obj node when the input param is ref or ptr.
            if idx > 0 && idx <= param_len {
                if is_ptr(local_ty) {
                    var_map.insert(
                        idx,
                        VariableNode::new(
                            idx,
                            Some(locals.len() + obj_cnt),
                            HashSet::new(),
                            local_ty,
                            States::new_unknown(),
                        ),
                    );
                    var_map.insert(
                        locals.len() + obj_cnt,
                        VariableNode::new_with_states(
                            locals.len() + obj_cnt,
                            get_pointee(local_ty),
                            States::new_unknown(),
                        ),
                    );
                    obj_cnt = obj_cnt + 1;
                } else if is_ref(local_ty) {
                    var_map.insert(
                        idx,
                        VariableNode::new(
                            idx,
                            Some(locals.len() + obj_cnt),
                            HashSet::new(),
                            local_ty,
                            States::new(),
                        ),
                    );
                    var_map.insert(
                        locals.len() + obj_cnt,
                        VariableNode::new_with_states(
                            locals.len() + obj_cnt,
                            get_pointee(local_ty),
                            States::new(),
                        ),
                    );
                    obj_cnt = obj_cnt + 1;
                } else {
                    var_map.insert(idx, VariableNode::new_default(idx, local_ty));
                }
                continue;
            }
            var_map.insert(idx, VariableNode::new_default(idx, local_ty));
        }
        Self {
            tcx,
            def_id,
            local_len: locals.len(),
            variables: var_map,
        }
    }

    pub fn get_obj_ty_through_chain(&self, arg: usize) -> Option<Ty<'tcx>> {
        let var = self.variables.get(&arg)?;
        if !is_ptr(var.ty) && !is_ref(var.ty) {
            return Some(var.ty);
        }
        if let Some(pointed_idx) = var.points_to {
            let pointed_var = self.variables.get(&pointed_idx)?;
            return Some(pointed_var.ty);
        }
        None
    }

    pub fn get_point_to_id(&self, arg: usize) -> usize {
        let var = self.variables.get(&arg).unwrap();
        if !is_ptr(var.ty) && !is_ref(var.ty) {
            return arg;
        }
        if let Some(pointed_idx) = var.points_to {
            return pointed_idx;
        }
        arg
    }

    pub fn is_local(&self, node_id: usize) -> bool {
        self.local_len > node_id
    }
}

// This implementation has the auxiliary function of DominatedGraph,
// including c/r/u/d nodes, printing chains' structure.
impl<'tcx> DominatedGraph<'tcx> {
    pub fn get_or_insert_field(&mut self, local: usize, field_idx: usize, ty: Ty<'tcx>) -> usize {
        let map_len = self.variables.len();
        let node = self.variables.get(&local).unwrap();
        if let Some(alias_local) = node.field.get(&field_idx) {
            return *alias_local;
        }
        self.variables
            .insert(map_len, VariableNode::new_default(map_len, ty));
        let mut_node = self.variables.get_mut(&local).unwrap();
        mut_node.field.insert(field_idx, map_len);
        return map_len;
    }

    pub fn point(&mut self, lv: usize, rv: usize) {
        // rap_warn!("{lv} = {rv}");
        let rv_node = self.variables.get_mut(&rv).unwrap();
        rv_node.pointed_by.insert(lv);
        let lv_node = self.variables.get_mut(&lv).unwrap();
        let ori_to = lv_node.points_to.clone();
        lv_node.points_to = Some(rv);
        if let Some(to) = ori_to {
            let ori_to_node = self.variables.get_mut(&to).unwrap();
            ori_to_node.pointed_by.remove(&lv);
        }
    }

    pub fn merge(&mut self, lv: usize, rv: usize) {
        let rv_node = self.variables.get_mut(&rv).unwrap().clone();
        let lv_node = self.variables.get_mut(&lv).unwrap();
        lv_node.points_to = rv_node.points_to;
        lv_node.states = rv_node.states;
        if let Some(to) = &rv_node.points_to {
            let ori_to_node = self.variables.get_mut(&to).unwrap();
            ori_to_node.pointed_by.insert(lv);
        }
    }

    pub fn insert_node(&mut self, dv: usize, ty: Ty<'tcx>) {
        if self.variables.get(&dv).is_none() {
            self.variables.insert(dv, VariableNode::new_default(dv, ty));
        }
    }

    pub fn delete_node(&mut self, idx: usize) {
        let node = self.variables.get(&idx).unwrap().clone();
        for pre_idx in &node.pointed_by.clone() {
            let pre_node = self.variables.get_mut(pre_idx).unwrap();
            pre_node.points_to = None;
        }
        if let Some(to) = &node.points_to.clone() {
            let next_node = self.variables.get_mut(&to).unwrap();
            next_node.pointed_by.remove(&idx);
        }
        self.variables.remove(&idx);
    }

    pub fn print_graph(&self) {
        let mut visited = HashSet::new();
        let mut subgraphs = Vec::new();

        // 找到所有连通子图
        for &node_id in self.variables.keys() {
            if !visited.contains(&node_id) {
                let mut queue = VecDeque::new();
                let mut subgraph = Vec::new();

                queue.push_back(node_id);
                visited.insert(node_id);

                while let Some(current_id) = queue.pop_front() {
                    subgraph.push(current_id);

                    if let Some(node) = self.variables.get(&current_id) {
                        if let Some(next_id) = node.points_to {
                            if !visited.contains(&next_id) {
                                visited.insert(next_id);
                                queue.push_back(next_id);
                            }
                        }

                        for &pointer_id in &node.pointed_by {
                            if !visited.contains(&pointer_id) {
                                visited.insert(pointer_id);
                                queue.push_back(pointer_id);
                            }
                        }
                    }
                }

                subgraphs.push(subgraph);
            }
        }

        for (i, mut subgraph) in subgraphs.into_iter().enumerate() {
            subgraph.sort_unstable();
            println!("Connected Subgraph {}: {:?}", i + 1, subgraph);

            for node_id in subgraph {
                if let Some(node) = self.variables.get(&node_id) {
                    println!("  Node {} → {:?}", node_id, node.points_to);
                }
            }
            println!();
        }
    }
}
