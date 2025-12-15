use crate::{
    analysis::{
        senryx::{
            contracts::{
                abstract_state::AlignState,
                property::{CisRangeItem, ContractualInvariantState, PropertyContract},
            },
            symbolic_analysis::{AnaOperand, SymbolicDef},
        },
        utils::fn_info::{display_hashmap, get_pointee, is_ptr, is_ref, is_slice, reverse_op},
    },
    rap_debug, rap_warn,
};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::BinOp;
use rustc_middle::mir::Local;
use rustc_middle::ty::TyKind;
use rustc_middle::ty::{Ty, TyCtxt};
use serde::de;
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct States<'tcx> {
    pub nonnull: bool,
    pub allocator_consistency: bool,
    pub init: bool,
    pub align: AlignState<'tcx>,
    pub valid_string: bool,
    pub valid_cstr: bool,
}

impl<'tcx> States<'tcx> {
    pub fn new(ty: Ty<'tcx>) -> Self {
        Self {
            nonnull: true,
            allocator_consistency: true,
            init: true,
            align: AlignState::Aligned(ty, 0),
            valid_string: true,
            valid_cstr: true,
        }
    }

    pub fn new_unknown() -> Self {
        Self {
            nonnull: false,
            allocator_consistency: false,
            init: false,
            align: AlignState::Unknown,
            valid_string: false,
            valid_cstr: false,
        }
    }

    pub fn merge_states(&mut self, other: &States<'tcx>) {
        self.nonnull &= other.nonnull;
        self.allocator_consistency &= other.allocator_consistency;
        self.init &= other.init;
        self.align.merge(&other.align);
        self.valid_string &= other.valid_string;
        self.valid_cstr &= other.valid_cstr;
    }
}

#[derive(Debug, Clone)]
pub struct InterResultNode<'tcx> {
    pub point_to: Option<Box<InterResultNode<'tcx>>>,
    pub fields: HashMap<usize, InterResultNode<'tcx>>,
    pub ty: Option<Ty<'tcx>>,
    pub states: States<'tcx>,
    pub const_value: usize,
}

impl<'tcx> InterResultNode<'tcx> {
    pub fn new_default(ty: Option<Ty<'tcx>>) -> Self {
        Self {
            point_to: None,
            fields: HashMap::new(),
            ty,
            states: States::new(ty.unwrap()),
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
            states: var_node.ots.clone(),
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

#[derive(Clone, Debug)]
pub struct FunctionSummary {
    pub return_def: Option<SymbolicDef>,
}

impl FunctionSummary {
    pub fn new(def: Option<SymbolicDef>) -> Self {
        Self { return_def: def }
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
    pub ots: States<'tcx>,
    pub const_value: usize,
    pub cis: ContractualInvariantState<'tcx>,
    pub offset_from: Option<SymbolicDef>,
}

impl<'tcx> VariableNode<'tcx> {
    pub fn new(
        id: usize,
        points_to: Option<usize>,
        pointed_by: HashSet<usize>,
        ty: Option<Ty<'tcx>>,
        ots: States<'tcx>,
    ) -> Self {
        VariableNode {
            id,
            alias_set: HashSet::from([id]),
            points_to,
            pointed_by,
            field: HashMap::new(),
            ty,
            is_dropped: false,
            ots,
            const_value: 0,
            cis: ContractualInvariantState::new_default(),
            offset_from: None,
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
            ots: States::new(ty.unwrap()),
            const_value: 0,
            cis: ContractualInvariantState::new_default(),
            offset_from: None,
        }
    }

    pub fn new_with_states(id: usize, ty: Option<Ty<'tcx>>, ots: States<'tcx>) -> Self {
        VariableNode {
            id,
            alias_set: HashSet::from([id]),
            points_to: None,
            pointed_by: HashSet::new(),
            field: HashMap::new(),
            ty,
            is_dropped: false,
            ots,
            const_value: 0,
            cis: ContractualInvariantState::new_default(),
            offset_from: None,
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
                node.ots.init = false;
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
        node.ots = inter_result.states;
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
        // init arg nodes' point to nodes.
        let body = self.tcx.optimized_mir(self.def_id);
        let locals = body.local_decls.clone();
        let fn_sig = self.tcx.fn_sig(self.def_id).skip_binder();
        let param_len = fn_sig.inputs().skip_binder().len();
        for idx in 1..param_len + 1 {
            let local_ty = locals[Local::from(idx)].ty;
            self.generate_ptr_with_obj_node(local_ty, idx);
        }
        // init args' cis
        let cis_results = crate::analysis::utils::fn_info::generate_contract_from_annotation(
            self.tcx,
            self.def_id,
        );
        for (base, fields, contract) in cis_results {
            if fields.len() == 0 {
                self.insert_cis_for_arg(base, contract);
            } else {
                let mut cur_base = base;
                let mut field_node = base;
                for field in fields {
                    field_node = self.insert_field_node(cur_base, field.0, Some(field.1));
                    // check if field's type is ptr or ref: yes -> create shadow var
                    self.generate_ptr_with_obj_node(field.1, field_node);
                    cur_base = field_node;
                }
                self.insert_cis_for_arg(field_node, contract);
            }
        }
    }

    fn insert_cis_for_arg(&mut self, local: usize, contract: PropertyContract<'tcx>) {
        let node = self.get_var_node_mut(local).unwrap();
        node.cis.add_contract(contract);
    }

    /// When generate obj node, this function will add InBound Sp automatically.
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
            self.add_bound_for_obj(new_id, local_ty);
        } else if is_ref(local_ty) {
            // modify ptr node pointed
            self.get_var_node_mut(idx).unwrap().points_to = Some(new_id);
            // insert ref object node
            self.insert_node(
                new_id,
                Some(get_pointee(local_ty)),
                idx,
                None,
                States::new(local_ty),
            );
            self.add_bound_for_obj(new_id, local_ty);
        }
        new_id
    }

    fn add_bound_for_obj(&mut self, new_id: usize, local_ty: Ty<'tcx>) {
        let new_node = self.get_var_node_mut(new_id).unwrap();
        let new_node_ty = get_pointee(local_ty);
        let contract = if is_slice(new_node_ty).is_some() {
            let inner_ty = is_slice(new_node_ty).unwrap();
            PropertyContract::new_obj_boundary(inner_ty, CisRangeItem::new_unknown())
        } else {
            PropertyContract::new_obj_boundary(new_node_ty, CisRangeItem::new_value(1))
        };
        new_node.cis.add_contract(contract);
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

    pub fn find_var_id_with_fields_seq(&mut self, local: usize, fields: &Vec<usize>) -> usize {
        let mut cur = local;
        for field in fields.clone() {
            let mut cur_node = self.get_var_node(cur).unwrap();
            if let TyKind::Ref(_, ty, _) = cur_node.ty.unwrap().kind() {
                let point_to = self.get_point_to_id(cur);
                cur_node = self.get_var_node(point_to).unwrap();
            }
            // If there exist a field node, then get it as cur node
            if cur_node.field.get(&field).is_some() {
                cur = *cur_node.field.get(&field).unwrap();
                continue;
            }
            // Otherwise, insert a new field node.
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
                    rap_warn!("ty {:?}, field: {:?}", cur_node.ty.unwrap(), field);
                    rap_warn!(
                        "set field type as None! --- src: Dominated Graph / find_var_id_with_fields_seq"
                    );
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
        let lv_states = lv_node.ots.clone();
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
        lv_node.ots = rv_node.ots;
        lv_node.cis = rv_node.cis;
        lv_node.is_dropped = rv_node.is_dropped;
        let lv_id = lv_node.id;
        // if is_ptr(rv_node.ty.unwrap()) && is_ptr(lv_ty) {
        //     // println!("++++{lv}--{rv}");
        //     self.merge(lv, rv);
        // }
        if rv_node.points_to.is_some() {
            self.point(lv_id, rv_node.points_to.unwrap());
        }
    }

    fn break_node_connection(&mut self, lv: usize, rv: usize) {
        let rv_node = self.get_var_node_mut(rv).unwrap();
        rv_node.pointed_by.remove(&lv);
        let lv_node = self.get_var_node_mut(lv).unwrap();
        lv_node.points_to = None;
    }

    fn insert_node(
        &mut self,
        dv: usize,
        ty: Option<Ty<'tcx>>,
        parent_id: usize,
        child_id: Option<usize>,
        state: States<'tcx>,
    ) {
        self.variables.insert(
            dv,
            VariableNode::new(dv, child_id, HashSet::from([parent_id]), ty, state),
        );
    }

    fn delete_node(&mut self, idx: usize) {
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
        node.ots.init = true;
    }

    pub fn insert_patial_op(&mut self, p1: usize, p2: usize, op: &BinOp) {
        let p1_node = self.get_var_node_mut(p1).unwrap();
        p1_node
            .cis
            .add_contract(PropertyContract::new_patial_order(p2, *op));
        let p2_node = self.get_var_node_mut(p2).unwrap();
        p2_node
            .cis
            .add_contract(PropertyContract::new_patial_order(p1, reverse_op(*op)));
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

use std::fmt::Write;
impl<'tcx> DominatedGraph<'tcx> {
    pub fn to_dot_graph(&self) -> String {
        let mut dot = String::new();
        writeln!(dot, "digraph DominatedGraph {{").unwrap();

        writeln!(
            dot,
            "    graph [compound=true, splines=polyline, nodesep=0.5, ranksep=0.5];"
        )
        .unwrap();
        writeln!(dot, "    node [shape=plain, fontname=\"Courier\"];").unwrap();
        writeln!(dot, "    edge [fontname=\"Courier\"];").unwrap();

        let mut isolated_nodes = Vec::new();
        let mut connected_nodes = Vec::new();

        let mut keys: Vec<&usize> = self.variables.keys().collect();
        keys.sort();

        for id in keys {
            if let Some(node) = self.variables.get(id) {
                let is_isolated =
                    node.points_to.is_none() && node.field.is_empty() && node.pointed_by.is_empty();

                if is_isolated {
                    isolated_nodes.push(*id);
                } else {
                    connected_nodes.push(*id);
                }
            }
        }

        if !isolated_nodes.is_empty() {
            writeln!(dot, "    subgraph cluster_isolated {{").unwrap();
            writeln!(dot, "        label = \"Isolated Variables (Grid Layout)\";").unwrap();
            writeln!(dot, "        style = dashed;").unwrap();
            writeln!(dot, "        color = grey;").unwrap();

            let total_iso = isolated_nodes.len();
            let cols = (total_iso as f64).sqrt().ceil() as usize;

            for id in &isolated_nodes {
                if let Some(node) = self.variables.get(id) {
                    let node_label = self.generate_node_label(node);
                    writeln!(dot, "        {} [label=<{}>];", id, node_label).unwrap();
                }
            }

            for chunk in isolated_nodes.chunks(cols) {
                write!(dot, "        {{ rank=same;").unwrap();
                for id in chunk {
                    write!(dot, " {};", id).unwrap();
                }
                writeln!(dot, " }}").unwrap();
            }

            for i in 0..isolated_nodes.chunks(cols).len() {
                let current_row_idx = i * cols;
                let next_row_idx = (i + 1) * cols;

                if next_row_idx < total_iso {
                    let curr_id = isolated_nodes[current_row_idx];
                    let next_id = isolated_nodes[next_row_idx];
                    writeln!(
                        dot,
                        "        {} -> {} [style=invis, weight=100];",
                        curr_id, next_id
                    )
                    .unwrap();
                }
            }

            writeln!(dot, "    }}").unwrap();
        }

        if !connected_nodes.is_empty() {
            writeln!(dot, "    subgraph cluster_connected {{").unwrap();
            writeln!(dot, "        label = \"Reference Graph\";").unwrap();
            writeln!(dot, "        color = black;").unwrap();

            for id in &connected_nodes {
                if let Some(node) = self.variables.get(id) {
                    let node_label = self.generate_node_label(node);
                    writeln!(dot, "        {} [label=<{}>];", id, node_label).unwrap();
                }
            }
            writeln!(dot, "    }}").unwrap();
        }

        // draw edges
        writeln!(dot, "").unwrap();
        for id in &connected_nodes {
            if let Some(node) = self.variables.get(id) {
                if let Some(target) = node.points_to {
                    writeln!(
                        dot,
                        "    {} -> {} [label=\"ptr\", color=\"blue\", fontcolor=\"blue\"];",
                        id, target
                    )
                    .unwrap();
                }

                let mut field_indices: Vec<&usize> = node.field.keys().collect();
                field_indices.sort();
                for field_idx in field_indices {
                    let target_id = node.field.get(field_idx).unwrap();
                    writeln!(
                        dot,
                        "    {} -> {} [label=\".{}\", style=\"dashed\"];",
                        id, target_id, field_idx
                    )
                    .unwrap();
                }
            }
        }

        writeln!(dot, "}}").unwrap();
        dot
    }

    fn generate_node_label(&self, node: &VariableNode<'tcx>) -> String {
        let ty_str = match node.ty {
            Some(t) => format!("{:?}", t),
            None => "None".to_string(),
        };
        let safe_ty = html_escape(&ty_str);

        format!(
            r#"<table border="0" cellborder="1" cellspacing="0" cellpadding="4">
                <tr><td colspan="2"><b>ID: {}</b></td></tr>
                <tr><td align="left">Type:</td><td align="left">{}</td></tr>
                <tr><td align="left">Const:</td><td align="left">{}</td></tr>
               </table>"#,
            node.id, safe_ty, node.const_value,
        )
    }
}

fn html_escape(input: &str) -> String {
    input
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace("\"", "&quot;")
}

impl<'tcx> DominatedGraph<'tcx> {
    /// Apply function summary to current DG
    /// dest_local: ret_val of the function call
    /// summary: summary of callee
    /// args: args of ftunction call
    pub fn apply_function_summary(
        &mut self,
        dest_local: usize,
        summary: &FunctionSummary,
        args: &Vec<usize>,
    ) {
        if let Some(def) = &summary.return_def {
            self.apply_summary_def(dest_local, def, args);
        }
    }

    // Dispatcher of function summary,
    // 'SymbolicDef' will record the relationship between params and ret_val.
    fn apply_summary_def(&mut self, target_local: usize, def: &SymbolicDef, args: &Vec<usize>) {
        match def {
            SymbolicDef::Param(param_idx) => {
                if *param_idx > 0 && param_idx - 1 < args.len() {
                    let arg_local = args[param_idx - 1];
                    self.merge(target_local, arg_local);
                }
            }
            SymbolicDef::Binary(BinOp::Offset, param_base_idx, rhs_op) => {
                if *param_base_idx > 0 && param_base_idx - 1 < args.len() {
                    let base_local = args[param_base_idx - 1];
                    let base_point_to = self.get_point_to_id(base_local);

                    self.point(target_local, base_point_to);

                    let node = self.get_var_node_mut(target_local).unwrap();
                    let real_rhs_op = match rhs_op {
                        AnaOperand::Const(c) => AnaOperand::Const(*c),
                        AnaOperand::Local(param_idx) => {
                            if *param_idx > 0 && param_idx - 1 < args.len() {
                                AnaOperand::Local(args[param_idx - 1])
                            } else {
                                AnaOperand::Const(0)
                            }
                        }
                    };

                    node.offset_from =
                        Some(SymbolicDef::Binary(BinOp::Offset, base_local, real_rhs_op));

                    rap_warn!(
                        "Applied Offset summary: _{} is offset of _{} (arg {})",
                        target_local,
                        base_local,
                        param_base_idx
                    );
                }
            }
            // todo: support others.
            _ => {}
        }
    }
}
