use crate::{
    analysis::utils::fn_info::{display_hashmap, get_pointee, is_ptr, is_ref},
    rap_warn,
};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Local;
use rustc_middle::ty::{Ty, TyCtxt};
use std::collections::{HashMap, HashSet, VecDeque};

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
    pub alias_set: HashSet<usize>,
    points_to: Option<usize>,
    pointed_by: HashSet<usize>,
    pub field: HashMap<usize, usize>,
    pub ty: Option<Ty<'tcx>>,
    pub is_dropped: bool,
    pub states: States,
}

impl<'tcx> VariableNode<'tcx> {
    pub fn new(
        id: usize,
        points_to: Option<usize>,
        pointed_by: HashSet<usize>,
        ty: Option<Ty<'tcx>>,
        states: States,
    ) -> Self {
        VariableNode {
            id,
            alias_set: HashSet::from([id]),
            points_to,
            pointed_by,
            field: HashMap::new(),
            ty,
            is_dropped: false,
            states,
        }
    }

    pub fn new_default(id: usize, ty: Option<Ty<'tcx>>) -> Self {
        VariableNode {
            id,
            alias_set: HashSet::from([id]),
            points_to: None,
            pointed_by: HashSet::new(),
            field: HashMap::new(),
            ty,
            is_dropped: false,
            states: States::new(),
        }
    }

    pub fn new_with_states(id: usize, ty: Option<Ty<'tcx>>, states: States) -> Self {
        VariableNode {
            id,
            alias_set: HashSet::from([id]),
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
    pub local_len: usize,
    pub variables: HashMap<usize, VariableNode<'tcx>>,
}

impl<'tcx> DominatedGraph<'tcx> {
    // This constructor will init all the local arguments' node states.
    // If input argument is ptr or ref, it will point to a corresponding obj node.
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
                    // insert ptr node
                    var_map.insert(
                        idx,
                        VariableNode::new(
                            idx,
                            Some(locals.len() + obj_cnt),
                            HashSet::new(),
                            Some(local_ty),
                            States::new_unknown(),
                        ),
                    );
                    // insert pointed object node
                    var_map.insert(
                        locals.len() + obj_cnt,
                        VariableNode::new(
                            locals.len() + obj_cnt,
                            None,
                            HashSet::from([idx]),
                            Some(get_pointee(local_ty)),
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
                            Some(local_ty),
                            States::new(),
                        ),
                    );
                    var_map.insert(
                        locals.len() + obj_cnt,
                        VariableNode::new(
                            locals.len() + obj_cnt,
                            None,
                            HashSet::from([idx]),
                            Some(get_pointee(local_ty)),
                            States::new(),
                        ),
                    );
                    obj_cnt = obj_cnt + 1;
                } else {
                    var_map.insert(idx, VariableNode::new_default(idx, Some(local_ty)));
                }
                continue;
            }
            var_map.insert(idx, VariableNode::new_default(idx, Some(local_ty)));
        }
        Self {
            tcx,
            def_id,
            local_len: locals.len(),
            variables: var_map,
        }
    }

    pub fn get_local_ty_by_place(&self, arg: usize) -> Option<Ty<'tcx>> {
        let body = self.tcx.optimized_mir(self.def_id);
        let locals = body.local_decls.clone();
        if arg < locals.len() {
            return Some(locals[Local::from(arg)].ty);
        } else {
            // If the arg is a field of some place, we search the whole map for it.
            return self.get_var_node(arg).unwrap().ty;
        }
    }

    pub fn get_obj_ty_through_chain(&self, arg: usize) -> Option<Ty<'tcx>> {
        let var = self.get_var_node(arg).unwrap();
        // If the var is ptr or ref, then find its pointed obj.
        if let Some(pointed_idx) = var.points_to {
            let pointed_var = self.get_var_node(pointed_idx).unwrap();
            return pointed_var.ty;
        } else {
            return var.ty;
        }
    }

    pub fn get_point_to_id(&self, arg: usize) -> usize {
        // display_hashmap(&self.variables,1);
        // println!("{:?}",self.def_id);
        let var = self.get_var_node(arg).unwrap();
        if let Some(pointed_idx) = var.points_to {
            return pointed_idx;
        } else {
            return arg;
        }
    }

    pub fn is_local(&self, node_id: usize) -> bool {
        self.local_len > node_id
    }
}

// This implementation has the auxiliary function of DominatedGraph,
// including c/r/u/d nodes and printing chains' structure.
impl<'tcx> DominatedGraph<'tcx> {
    // Only for inserting field obj node or pointed obj node.
    pub fn generate_node_id(&self) -> usize {
        if self.variables.len() == 0 || *self.variables.keys().max().unwrap() < self.local_len {
            return self.local_len;
        }
        return *self.variables.keys().max().unwrap() + 1;
    }

    pub fn get_field_node_id(
        &mut self,
        local: usize,
        field_idx: usize,
        ty: Option<Ty<'tcx>>,
    ) -> usize {
        let node = self.get_var_node(local).unwrap();
        if let Some(alias_local) = node.field.get(&field_idx) {
            return *alias_local;
        } else {
            self.insert_field_node(local, field_idx, ty)
        }
    }

    // Insert the responding field node of one local, then return its genrated node_id.
    pub fn insert_field_node(
        &mut self,
        local: usize,
        field_idx: usize,
        ty: Option<Ty<'tcx>>,
    ) -> usize {
        let new_id = self.generate_node_id();
        self.variables
            .insert(new_id, VariableNode::new_default(new_id, ty));
        let mut_node = self.get_var_node_mut(local).unwrap();
        mut_node.field.insert(field_idx, new_id);
        return new_id;
    }

    pub fn find_var_id_with_fields_seq(&mut self, local: usize, fields: Vec<usize>) -> usize {
        let mut cur = local;
        for field in fields {
            cur = self.get_field_node_id(cur, field, None);
        }
        return cur;
    }

    pub fn point(&mut self, lv: usize, rv: usize) {
        // rap_warn!("{lv} = & or * {rv}");
        let rv_node = self.get_var_node_mut(rv).unwrap();
        rv_node.pointed_by.insert(lv);
        let lv_node = self.get_var_node_mut(lv).unwrap();
        let ori_to = lv_node.points_to.clone();
        lv_node.points_to = Some(rv);
        // Delete lv from the origin pointed node's pointed_by.
        if let Some(to) = ori_to {
            let ori_to_node = self.get_var_node_mut(to).unwrap();
            ori_to_node.pointed_by.remove(&lv);
        }
    }

    pub fn get_var_node(&self, local_id: usize) -> Option<&VariableNode<'tcx>> {
        for (_idx, var_node) in &self.variables {
            if var_node.alias_set.contains(&local_id) {
                return Some(var_node);
            }
        }
        rap_warn!("def id:{:?}, local_id: {local_id}", self.def_id);
        display_hashmap(&self.variables, 1);
        None
    }

    pub fn get_var_node_mut(&mut self, local_id: usize) -> Option<&mut VariableNode<'tcx>> {
        let va = self.variables.clone();
        for (_idx, var_node) in &mut self.variables {
            if var_node.alias_set.contains(&local_id) {
                return Some(var_node);
            }
        }
        rap_warn!("def id:{:?}, local_id: {local_id}", self.def_id);
        display_hashmap(&va, 1);
        None
    }

    // Merge node when (lv = move rv);
    // In this case, lv will be the same with rv.
    pub fn merge(&mut self, lv: usize, rv: usize) {
        let rv_node = self.get_var_node_mut(rv).unwrap();
        rv_node.alias_set.insert(lv);
        if let Some(lv_node) = self.get_var_node_mut(lv) {
            lv_node.alias_set.remove(&lv);
        }
    }

    // Called when (lv = copy rv);
    pub fn copy_node(&mut self, lv: usize, rv: usize) {
        let rv_node = self.get_var_node_mut(rv).unwrap().clone();
        let lv_node = self.get_var_node_mut(lv).unwrap();
        lv_node.states = rv_node.states;
        lv_node.is_dropped = rv_node.is_dropped;
        if let Some(to) = &rv_node.points_to {
            self.point(lv, *to);
        }
    }

    pub fn break_node_connection(&mut self, lv: usize, rv: usize) {
        let rv_node = self.get_var_node_mut(rv).unwrap();
        rv_node.pointed_by.remove(&lv);
        let lv_node = self.get_var_node_mut(lv).unwrap();
        lv_node.points_to = None;
    }

    pub fn insert_node(&mut self, dv: usize, ty: Option<Ty<'tcx>>) {
        if let Some(ori_node) = self.get_var_node_mut(dv) {
            ori_node.alias_set.remove(&dv);
        }
        self.variables.insert(dv, VariableNode::new_default(dv, ty));
    }

    pub fn delete_node(&mut self, idx: usize) {
        let node = self.get_var_node(idx).unwrap().clone();
        for pre_idx in &node.pointed_by.clone() {
            let pre_node = self.get_var_node_mut(*pre_idx).unwrap();
            pre_node.points_to = None;
        }
        if let Some(to) = &node.points_to.clone() {
            let next_node = self.get_var_node_mut(*to).unwrap();
            next_node.pointed_by.remove(&idx);
        }
        self.variables.remove(&idx);
    }

    pub fn set_drop(&mut self, idx: usize) {
        if let Some(ori_node) = self.get_var_node_mut(idx) {
            if ori_node.is_dropped == true {
                rap_warn!("Double free detected!"); // todo: update reports
            }
            ori_node.is_dropped = true;
        }
    }

    pub fn print_graph(&self) {
        let mut visited = HashSet::new();
        let mut subgraphs = Vec::new();

        for &node_id in self.variables.keys() {
            if !visited.contains(&node_id) {
                let mut queue = VecDeque::new();
                let mut subgraph = Vec::new();

                queue.push_back(node_id);
                visited.insert(node_id);

                while let Some(current_id) = queue.pop_front() {
                    subgraph.push(current_id);

                    if let Some(node) = self.get_var_node(current_id) {
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
                if let Some(node) = self.get_var_node(node_id) {
                    println!("  Node {} → {:?}", node_id, node.points_to);
                }
            }
            println!();
        }
    }
}
