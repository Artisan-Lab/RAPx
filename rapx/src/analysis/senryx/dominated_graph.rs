use crate::{
    analysis::{
        senryx::contracts::{
            contract,
            property::{ContractualInvariantState, PropertyContract},
        },
        utils::fn_info::{display_hashmap, get_pointee, is_ptr, is_ref},
    },
    rap_warn,
};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Local;
use rustc_middle::ty::TyKind;
use rustc_middle::ty::{Ty, TyCtxt};
use serde::de;
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct States {
    pub nonnull: bool,
    pub allocator_consistency: bool,
    pub init: bool,
    pub align: bool,
    pub valid_string: bool,
    pub valid_cstr: bool,
}

impl States {
    pub fn new() -> Self {
        Self {
            nonnull: true,
            allocator_consistency: true,
            init: true,
            align: true,
            valid_string: true,
            valid_cstr: true,
        }
    }

    pub fn new_unknown() -> Self {
        Self {
            nonnull: false,
            allocator_consistency: false,
            init: false,
            align: false,
            valid_string: false,
            valid_cstr: false,
        }
    }

    pub fn merge_states(&mut self, other: &States) {
        self.nonnull &= other.nonnull;
        self.allocator_consistency &= other.allocator_consistency;
        self.init &= other.init;
        self.align &= other.align;
        self.valid_string &= other.valid_string;
        self.valid_cstr &= other.valid_cstr;
    }
}

#[derive(Debug, Clone)]
pub struct InterResultNode<'tcx> {
    pub point_to: Option<Box<InterResultNode<'tcx>>>,
    pub fields: HashMap<usize, InterResultNode<'tcx>>,
    pub ty: Option<Ty<'tcx>>,
    pub states: States,
    pub const_value: usize,
}

impl<'tcx> InterResultNode<'tcx> {
    pub fn new_default(ty: Option<Ty<'tcx>>) -> Self {
        Self {
            point_to: None,
            fields: HashMap::new(),
            ty,
            states: States::new(),
            const_value: 0, // To be modified
        }
    }

    pub fn construct_from_var_node(chain: DominatedGraph<'tcx>, var_id: usize) -> Self {
        let var_node = chain.get_var_node(var_id).unwrap();
        let point_node = if var_node.points_to.is_none() {
            None
        } else {
            Some(Box::new(Self::construct_from_var_node(
                chain.clone(),
                var_node.points_to.unwrap(),
            )))
        };
        let fields = var_node
            .field
            .iter()
            .map(|(k, v)| (*k, Self::construct_from_var_node(chain.clone(), *v)))
            .collect();
        Self {
            point_to: point_node,
            fields,
            ty: var_node.ty.clone(),
            states: var_node.states.clone(),
            const_value: var_node.const_value,
        }
    }

    pub fn merge(&mut self, other: InterResultNode<'tcx>) {
        if self.ty != other.ty {
            return;
        }
        // merge current node's states
        self.states.merge_states(&other.states);

        // merge node it points to
        match (&mut self.point_to, other.point_to) {
            (Some(self_ptr), Some(other_ptr)) => self_ptr.merge(*other_ptr),
            (None, Some(other_ptr)) => {
                self.point_to = Some(other_ptr.clone());
            }
            _ => {}
        }
        // merge the fields nodess
        for (field_id, other_node) in &other.fields {
            match self.fields.get_mut(field_id) {
                Some(self_node) => self_node.merge(other_node.clone()),
                None => {
                    self.fields.insert(*field_id, other_node.clone());
                }
            }
        }
        // TODO: merge into a range
        self.const_value = std::cmp::max(self.const_value, other.const_value);
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
    pub const_value: usize,
    pub cis: ContractualInvariantState<'tcx>,
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
            const_value: 0,
            cis: ContractualInvariantState::new_default(),
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
            const_value: 0,
            cis: ContractualInvariantState::new_default(),
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
            const_value: 0,
            cis: ContractualInvariantState::new_default(),
        }
    }
}

#[derive(Clone)]
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
        crate::analysis::utils::fn_info::generate_contract_from_annotation(tcx, def_id);
        let body = tcx.optimized_mir(def_id);
        let locals = body.local_decls.clone();
        let fn_sig = tcx.fn_sig(def_id).skip_binder();
        let param_len = fn_sig.inputs().skip_binder().len();
        let mut var_map: HashMap<usize, VariableNode<'_>> = HashMap::new();
        let mut obj_cnt = 0;
        for (idx, local) in locals.iter().enumerate() {
            let local_ty = local.ty;
            let mut node = VariableNode::new_default(idx, Some(local_ty));
            if local_ty.to_string().contains("MaybeUninit") {
                node.states.init = false;
            }
            var_map.insert(idx, node);
        }
        Self {
            tcx,
            def_id,
            local_len: locals.len(),
            variables: var_map,
        }
    }

    pub fn init_self_with_inter(&mut self, inter_result: InterResultNode<'tcx>) {
        let self_node = self.get_var_node(1).unwrap().clone();
        if self_node.ty.unwrap().is_ref() {
            let obj_node = self.get_var_node(self.get_point_to_id(1)).unwrap();
            self.dfs_insert_inter_results(inter_result, obj_node.id);
        } else {
            self.dfs_insert_inter_results(inter_result, self_node.id);
        }
    }

    pub fn dfs_insert_inter_results(&mut self, inter_result: InterResultNode<'tcx>, local: usize) {
        let new_id = self.generate_node_id();
        let node = self.get_var_node_mut(local).unwrap();
        // node.ty = inter_result.ty;
        node.states = inter_result.states;
        node.const_value = inter_result.const_value;
        if inter_result.point_to.is_some() {
            let new_node = inter_result.point_to.unwrap();
            node.points_to = Some(new_id);
            self.insert_node(
                new_id,
                new_node.ty.clone(),
                local,
                None,
                new_node.states.clone(),
            );
            self.dfs_insert_inter_results(*new_node, new_id);
        }
        for (field_idx, field_inter) in inter_result.fields {
            let field_node_id = self.insert_field_node(local, field_idx, field_inter.ty.clone());
            self.dfs_insert_inter_results(field_inter, field_node_id);
        }
    }

    pub fn init_arg(&mut self) {
        let body = self.tcx.optimized_mir(self.def_id);
        let locals = body.local_decls.clone();
        let fn_sig = self.tcx.fn_sig(self.def_id).skip_binder();
        let param_len = fn_sig.inputs().skip_binder().len();
        for idx in 1..param_len + 1 {
            let local_ty = locals[Local::from(idx)].ty;
            self.generate_ptr_with_obj_node(local_ty, idx);
        }
    }

    pub fn generate_ptr_with_obj_node(&mut self, local_ty: Ty<'tcx>, idx: usize) -> usize {
        let new_id = self.generate_node_id();
        if is_ptr(local_ty) {
            // modify ptr node pointed
            self.get_var_node_mut(idx).unwrap().points_to = Some(new_id);
            // insert pointed object node
            self.insert_node(
                new_id,
                Some(get_pointee(local_ty)),
                idx,
                None,
                States::new_unknown(),
            );
        } else if is_ref(local_ty) {
            // modify ptr node pointed
            self.get_var_node_mut(idx).unwrap().points_to = Some(new_id);
            // insert ref object node
            self.insert_node(
                new_id,
                Some(get_pointee(local_ty)),
                idx,
                None,
                States::new(),
            );
        }
        new_id
    }

    // if current node is ptr or ref, then return the new node pointed by it.
    pub fn check_ptr(&mut self, arg: usize) -> usize {
        if self.get_var_node_mut(arg).unwrap().ty.is_none() {
            display_hashmap(&self.variables, 1);
        };
        let node_ty = self.get_var_node_mut(arg).unwrap().ty.unwrap();
        if is_ptr(node_ty) || is_ref(node_ty) {
            return self.generate_ptr_with_obj_node(node_ty, arg);
        }
        arg
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
            // let pointed_var = self.get_var_node(pointed_idx).unwrap();
            // pointed_var.ty
            self.get_obj_ty_through_chain(pointed_idx)
        } else {
            var.ty
        }
    }

    pub fn get_point_to_id(&self, arg: usize) -> usize {
        // display_hashmap(&self.variables,1);
        // println!("{:?}",self.def_id);
        let var = self.get_var_node(arg).unwrap();
        if let Some(pointed_idx) = var.points_to {
            pointed_idx
        } else {
            arg
        }
    }

    pub fn is_local(&self, node_id: usize) -> bool {
        self.local_len > node_id
    }
}

// This implementation has the auxiliary functions of DominatedGraph,
// including c/r/u/d nodes and printing chains' structure.
impl<'tcx> DominatedGraph<'tcx> {
    // Only for inserting field obj node or pointed obj node.
    pub fn generate_node_id(&self) -> usize {
        if self.variables.len() == 0 || *self.variables.keys().max().unwrap() < self.local_len {
            return self.local_len;
        }
        *self.variables.keys().max().unwrap() + 1
    }

    pub fn get_field_node_id(
        &mut self,
        local: usize,
        field_idx: usize,
        ty: Option<Ty<'tcx>>,
    ) -> usize {
        let node = self.get_var_node(local).unwrap();
        if let Some(alias_local) = node.field.get(&field_idx) {
            *alias_local
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
        let mut cur = self.get_point_to_id(local);
        for field in fields {
            cur = self.get_point_to_id(cur);
            let cur_node = self.get_var_node(cur).unwrap();
            match cur_node.ty.unwrap().kind() {
                TyKind::Adt(adt_def, substs) => {
                    if adt_def.is_struct() {
                        for (idx, field_def) in adt_def.all_fields().enumerate() {
                            if idx == field {
                                cur = self.get_field_node_id(
                                    cur,
                                    field,
                                    Some(field_def.ty(self.tcx, substs)),
                                );
                            }
                        }
                    }
                }
                // TODO: maybe unsafe here for setting ty as None!
                _ => {
                    cur = self.get_field_node_id(cur, field, None);
                }
            }
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

    pub fn get_var_nod_id(&self, local_id: usize) -> usize {
        self.get_var_node(local_id).unwrap().id
    }

    pub fn get_map_idx_node(&self, local_id: usize) -> &VariableNode<'tcx> {
        self.variables.get(&local_id).unwrap()
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
    // And the nodes pointing to lv originally will re-point to rv.
    pub fn merge(&mut self, lv: usize, rv: usize) {
        let lv_node = self.get_var_node_mut(lv).unwrap().clone();
        if lv_node.alias_set.contains(&rv) {
            return;
        }
        for lv_pointed_by in lv_node.pointed_by.clone() {
            self.point(lv_pointed_by, rv);
        }
        let lv_node = self.get_var_node_mut(lv).unwrap();
        lv_node.alias_set.remove(&lv);
        let lv_ty = lv_node.ty;
        let lv_states = lv_node.states.clone();
        let rv_node = self.get_var_node_mut(rv).unwrap();
        rv_node.alias_set.insert(lv);
        // rv_node.states.merge_states(&lv_states);
        if rv_node.ty.is_none() {
            rv_node.ty = lv_ty;
        }
    }

    // Called when (lv = copy rv);
    pub fn copy_node(&mut self, lv: usize, rv: usize) {
        let rv_node = self.get_var_node_mut(rv).unwrap().clone();
        let lv_node = self.get_var_node_mut(lv).unwrap();
        let lv_ty = lv_node.ty.unwrap();
        lv_node.states = rv_node.states;
        lv_node.is_dropped = rv_node.is_dropped;
        if is_ptr(rv_node.ty.unwrap()) && is_ptr(lv_ty) {
            // println!("++++{lv}--{rv}");
            self.merge(lv, rv);
        }
    }

    pub fn break_node_connection(&mut self, lv: usize, rv: usize) {
        let rv_node = self.get_var_node_mut(rv).unwrap();
        rv_node.pointed_by.remove(&lv);
        let lv_node = self.get_var_node_mut(lv).unwrap();
        lv_node.points_to = None;
    }

    pub fn insert_node(
        &mut self,
        dv: usize,
        ty: Option<Ty<'tcx>>,
        parent_id: usize,
        child_id: Option<usize>,
        state: States,
    ) {
        self.variables.insert(
            dv,
            VariableNode::new(dv, child_id, HashSet::from([parent_id]), ty, state),
        );
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

    pub fn set_drop(&mut self, idx: usize) -> bool {
        if let Some(ori_node) = self.get_var_node_mut(idx) {
            if ori_node.is_dropped == true {
                // rap_warn!("Double free detected!"); // todo: update reports
                return false;
            }
            ori_node.is_dropped = true;
        }
        true
    }

    pub fn update_value(&mut self, arg: usize, value: usize) {
        let node = self.get_var_node_mut(arg).unwrap();
        node.const_value = value;
        node.states.init = true;
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
