use super::{MopAAFact, MopAAResultMap, block::Term, corner_case::*, graph::*, types::*, value::*};
use crate::analysis::graphs::scc::Scc;
use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Operand, Place, ProjectionElem, TerminatorKind},
    ty,
};
use std::collections::HashSet;

impl<'tcx> MopGraph<'tcx> {
    /* alias analysis for a single block */
    pub fn alias_bb(&mut self, bb_index: usize) {
        for constant in self.blocks[bb_index].const_value.clone() {
            self.constants.insert(constant.local, constant.value);
        }
        let cur_block = self.blocks[bb_index].clone();
        for assign in cur_block.assignments {
            rap_debug!("assign: {:?}", assign);
            let lv_idx = self.projection(assign.lv);
            let rv_idx = self.projection(assign.rv);

            self.assign_alias(lv_idx, rv_idx);
            rap_debug!("Alias sets: {:?}", self.alias_sets)
        }
    }

    /* Check the aliases introduced by the terminators (function call) of a scc block */
    pub fn alias_bbcall(
        &mut self,
        bb_index: usize,
        fn_map: &mut MopAAResultMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        let cur_block = self.blocks[bb_index].clone();
        if let Term::Call(call) | Term::Drop(call) = cur_block.terminator {
            if let TerminatorKind::Call {
                func: Operand::Constant(ref constant),
                ref args,
                ref destination,
                target: _,
                unwind: _,
                call_source: _,
                fn_span: _,
            } = call.kind
            {
                let lv = self.projection(*destination);
                let mut merge_vec = Vec::new();
                merge_vec.push(lv);
                let mut may_drop_flag = 0;
                if self.values[lv].may_drop {
                    may_drop_flag += 1;
                }
                for arg in args {
                    match arg.node {
                        Operand::Copy(ref p) | Operand::Move(ref p) => {
                            let rv = self.projection(*p);
                            merge_vec.push(rv);
                            if self.values[rv].may_drop {
                                may_drop_flag += 1;
                            }
                        }
                        Operand::Constant(_) => {
                            merge_vec.push(0);
                        }
                    }
                }
                if let &ty::FnDef(target_id, _) = constant.const_.ty().kind() {
                    if may_drop_flag > 0 {
                        // This function does not introduce new aliases.
                        if is_corner_case(target_id) {
                            return;
                        }
                        if self.tcx.is_mir_available(target_id) {
                            rap_debug!("target_id {:?}", target_id);
                            if fn_map.contains_key(&target_id) {
                                let fn_aliases = fn_map.get(&target_id).unwrap();
                                rap_debug!("fn_aliases {:?}", fn_aliases);
                                for alias in fn_aliases.aliases().iter() {
                                    if !alias.valuable() {
                                        continue;
                                    }
                                    self.merge(alias, &merge_vec);
                                }
                            } else {
                                /* Fixed-point iteration: this is not perfect */
                                if recursion_set.contains(&target_id) {
                                    return;
                                }
                                recursion_set.insert(target_id);
                                let mut mop_graph = MopGraph::new(self.tcx, target_id);
                                mop_graph.find_scc();
                                mop_graph.check(0, fn_map, recursion_set);
                                let ret_alias = mop_graph.ret_alias.clone();
                                rap_info!("Alias of {:?}: {:?}", target_id, ret_alias);
                                for alias_pair in ret_alias.aliases().iter() {
                                    if !alias_pair.valuable() {
                                        continue;
                                    }
                                    self.merge(alias_pair, &merge_vec);
                                }
                                fn_map.insert(target_id, ret_alias);
                                recursion_set.remove(&target_id);
                            }
                        } else if self.values[lv].may_drop {
                            let mut right_set = Vec::new();
                            for rv in &merge_vec {
                                if self.values[*rv].may_drop
                                    && lv != *rv
                                    && self.values[lv].is_ptr()
                                {
                                    right_set.push(*rv);
                                }
                            }
                            if right_set.len() == 1 {
                                // TO FIX
                                self.sync_field_alias(lv, right_set[0], 0);
                            }
                        }
                    }
                }
            }
        }
    }

    /*
     * This is the function for field sensitivity
     * If the projection is a deref, we directly return its local;
     * If the projection is a field, we further make the id and its first element an alias.
     */
    pub fn projection(&mut self, place: Place<'tcx>) -> usize {
        let local = place.local.as_usize();
        rap_debug!("projection: place = {:?}, local = {:?}", place, local);
        let mut value_idx = local;
        // Projections are leveled
        // Case 1: (*6).1 involves two projections: a Deref and a Field.
        // Case 2: (6.0).1 involves two field projections.
        // We should recursively parse the projection.
        for proj in place.projection {
            rap_debug!("proj: {:?}", proj);
            let new_value_idx = self.values.len();
            match proj {
                ProjectionElem::Deref => {}
                ProjectionElem::Field(field, ty) => {
                    let field_idx = field.as_usize();
                    rap_info!("field_id = {}", field_idx);
                    // If the field has not been created as a value, we crate a value;
                    if !self.values[value_idx].fields.contains_key(&field_idx) {
                        let ty_env = ty::TypingEnv::post_analysis(self.tcx, self.def_id);
                        let need_drop = ty.needs_drop(self.tcx, ty_env);
                        let may_drop = !is_not_drop(self.tcx, ty);
                        let mut node =
                            Value::new(new_value_idx, local, need_drop, need_drop || may_drop);
                        node.kind = kind(ty);
                        node.field_id = field_idx;
                        node.father = value_idx;
                        self.values[value_idx].fields.insert(field_idx, node.index);
                        self.values.push(node);
                    }
                    value_idx = *self.values[value_idx].fields.get(&field_idx).unwrap();
                }
                _ => {}
            }
        }
        value_idx
    }

    pub fn assign_alias(&mut self, lv_idx: usize, rv_idx: usize) {
        rap_debug!("assign_alias: lv = {:?}. rv = {:?}", lv_idx, rv_idx);
        let r_set_idx = if let Some(idx) = self.find_alias_set(rv_idx) {
            idx
        } else {
            self.alias_sets
                .push([rv_idx].into_iter().collect::<FxHashSet<usize>>());
            self.alias_sets.len() - 1
        };

        if let Some(l_set_idx) = self.find_alias_set(lv_idx) {
            if l_set_idx == r_set_idx {
                return;
            }
            self.alias_sets[l_set_idx].remove(&lv_idx);
        }
        self.alias_sets[r_set_idx].insert(lv_idx);

        if self.values[lv_idx].fields.len() > 0 || self.values[rv_idx].fields.len() > 0 {
            self.sync_field_alias(lv_idx, rv_idx, 0);
        }
        if self.values[rv_idx].field_id != usize::MAX {
            self.sync_father_alias(lv_idx, rv_idx, r_set_idx);
        }
    }

    // Update the aliases of fields.
    // Case 1, lv = 1; rv = 2; field of rv: 1;
    // Expected result: [1,2] [1.1,2.1];
    // Case 2, lv = 0.0, rv = 7, field of rv: 0;
    // Expected result: [0.0,7] [0.0.0,7.0]
    pub fn sync_field_alias(&mut self, lv: usize, rv: usize, depth: usize) {
        rap_info!("sync field aliases for lv:{} rv:{}", lv, rv);

        let max_field_depth = match std::env::var_os("MOP") {
            Some(val) if val == "0" => 10,
            Some(val) if val == "1" => 20,
            Some(val) if val == "2" => 30,
            Some(val) if val == "3" => 50,
            _ => 15,
        };

        if depth > max_field_depth {
            return;
        }

        // For the fields of lv; we should remove them from the alias sets;
        //
        for lv_field in self.values[lv].fields.clone().into_iter() {
            if let Some(alias_set_idx) = self.find_alias_set(lv_field.1) {
                self.alias_sets[alias_set_idx].remove(&lv_field.1);
            }
        }

        for rv_field in self.values[rv].fields.clone().into_iter() {
            rap_debug!("rv_field: {:?}", rv_field);
            if !self.values[lv].fields.contains_key(&rv_field.0) {
                let mut node = Value::new(
                    self.values.len(),
                    self.values[lv].local,
                    self.values[rv_field.1].need_drop,
                    self.values[rv_field.1].may_drop,
                );
                node.kind = self.values[rv_field.1].kind;
                node.field_id = rv_field.0;
                self.values[lv].fields.insert(rv_field.0, node.index);
                self.values.push(node);
            }
            let lv_field_value_idx = *(self.values[lv].fields.get(&rv_field.0).unwrap());

            rap_debug!("alias_set_id of rv_field {:?}", self.find_alias_set(rv_field.1));
            if let Some(alias_set_idx) = self.find_alias_set(rv_field.1) {
                self.alias_sets[alias_set_idx].insert(lv_field_value_idx);
            }
            rap_debug!("alias sets: {:?}", self.alias_sets);
            self.sync_field_alias(lv_field_value_idx, rv_field.1, depth + 1);
        }
    }

    // For example,
    // Case 1: lv = 1; rv = 2.0; alias set [2, 3]
    // Expected result: [1, 2.0, 3.0], [2, 3];
    // Case 2: lv = 1.0; rv = 2; alias set [1, 3]
    // Expected result: [1.0, 2], [1, 3]
    pub fn sync_father_alias(&mut self, lv: usize, rv: usize, lv_alias_set_idx: usize) {
        rap_info!("sync father aliases for lv:{} rv:{}", lv, rv);
        let mut father_id = rv;
        let mut field_id = self.values[rv].field_id;
        while field_id != usize::MAX {
            father_id = self.values[father_id].father;
            let father_value = self.values[father_id].clone();
            if let Some(alias_set_idx) = self.find_alias_set(father_id) {
                for value_idx in self.alias_sets[alias_set_idx].clone() {
                    // create a new node if the node does not exist;
                    let field_value_idx = if self.values[value_idx].fields.contains_key(&field_id) {
                        *self.values[value_idx].fields.get(&field_id).unwrap()
                    } else {
                        let mut node = Value::new(
                            self.values.len(),
                            self.values[value_idx].local,
                            self.values[value_idx].need_drop,
                            self.values[value_idx].may_drop,
                        );
                        node.kind = self.values[value_idx].kind;
                        node.field_id = field_id;
                        self.values.push(node.clone());
                        self.values[value_idx].fields.insert(field_id, node.index);
                        node.index
                    };
                    // add the node to the alias_set of lv;
                    self.alias_sets[lv_alias_set_idx].insert(field_value_idx);
                }
            }
            field_id = father_value.field_id;
        }
    }

    //inter-procedure instruction to merge alias.
    pub fn merge(&mut self, ret_alias: &MopAAFact, arg_vec: &[usize]) {
        rap_debug!("{:?}", ret_alias);
        if ret_alias.lhs_no() >= arg_vec.len() || ret_alias.rhs_no() >= arg_vec.len() {
            return;
        }
        let left_init = arg_vec[ret_alias.lhs_no()];
        let right_init = arg_vec[ret_alias.rhs_no()];
        let mut lv = left_init;
        let mut rv = right_init;
        for index in ret_alias.lhs_fields().iter() {
            if !self.values[lv].fields.contains_key(index) {
                let need_drop = ret_alias.lhs_need_drop;
                let may_drop = ret_alias.lhs_may_drop;
                let mut node = Value::new(self.values.len(), left_init, need_drop, may_drop);
                node.kind = TyKind::RawPtr;
                node.field_id = *index;
                self.values[lv].fields.insert(*index, node.index);
                self.values.push(node);
            }
            lv = *self.values[lv].fields.get(index).unwrap();
        }
        let rv_local = self.values[rv].local;
        for index in ret_alias.rhs_fields().iter() {
            if !self.values[rv].fields.contains_key(index) {
                let need_drop = ret_alias.rhs_need_drop;
                let may_drop = ret_alias.rhs_may_drop;
                let mut node = Value::new(self.values.len(), rv_local, need_drop, may_drop);
                node.kind = TyKind::RawPtr;
                node.field_id = *index;
                self.values[rv].fields.insert(*index, node.index);
                self.values.push(node);
            }
            rv = *self.values[rv].fields.get(index).unwrap();
        }
        self.assign_alias(lv, rv);
    }

    pub fn get_field_seq(&self, value: &Value) -> Vec<usize> {
        let mut field_id_seq = vec![];
        let mut node_ref = value;
        while node_ref.field_id != usize::MAX {
            field_id_seq.push(node_ref.field_id);
            node_ref = &self.values[value.father];
        }
        field_id_seq
    }

    //merge the result of current path to the final result.
    pub fn merge_results(&mut self, results_nodes: Vec<Value>) {
        for node in results_nodes.iter() {
            if node.local > self.arg_size {
                continue;
            }
            let f_node: Vec<usize> = results_nodes.iter().map(|v| v.father).collect();
            for idx in 1..self.values.len() {
                if !self.is_aliasing(idx, node.index) {
                    continue;
                }

                let mut replace = None;
                if results_nodes[idx].local > self.arg_size {
                    for (i, &fidx) in f_node.iter().enumerate() {
                        if i != idx && i != node.index && fidx == f_node[idx] {
                            for (j, v) in results_nodes.iter().enumerate() {
                                if j != idx
                                    && j != node.index
                                    && self.is_aliasing(j, fidx)
                                    && v.local <= self.arg_size
                                {
                                    replace = Some(&results_nodes[j]);
                                }
                            }
                        }
                    }
                }

                if (results_nodes[idx].local <= self.arg_size || replace.is_some())
                    && idx != node.index
                    && node.local != results_nodes[idx].local
                {
                    let left_node;
                    let right_node;
                    match results_nodes[idx].local {
                        0 => {
                            left_node = match replace {
                                Some(replace_node) => replace_node,
                                None => &results_nodes[idx],
                            };
                            right_node = node;
                        }
                        _ => {
                            left_node = node;
                            right_node = match replace {
                                Some(replace_node) => replace_node,
                                None => &results_nodes[idx],
                            };
                        }
                    }
                    let mut new_alias = MopAAFact::new(
                        left_node.local,
                        left_node.may_drop,
                        left_node.need_drop,
                        right_node.local,
                        right_node.may_drop,
                        right_node.need_drop,
                    );
                    new_alias.fact.lhs_fields = self.get_field_seq(left_node);
                    new_alias.fact.rhs_fields = self.get_field_seq(right_node);
                    if new_alias.lhs_no() == 0 && new_alias.rhs_no() == 0 {
                        return;
                    }
                    rap_info!(
                        "new_alias.lhs_no = {:?}, rhs_no = {:?}, lhs_fields = {:?}, rhs_fields = {:?}",
                        new_alias.lhs_no(),
                        new_alias.rhs_no(),
                        new_alias.lhs_fields(),
                        new_alias.rhs_fields()
                    );
                    if new_alias.lhs_no() == new_alias.rhs_no()
                        && new_alias.lhs_fields() == new_alias.rhs_fields()
                    {
                        continue;
                    }
                    rap_info!("new_alias: {:?}", new_alias);
                    self.ret_alias.add_alias(new_alias);
                }
            }
        }
    }

    #[inline(always)]
    pub fn find_alias_set(&self, e: usize) -> Option<usize> {
        self.alias_sets.iter().position(|set| set.contains(&e))
    }

    #[inline(always)]
    pub fn is_aliasing(&mut self, e1: usize, e2: usize) -> bool {
        let s1 = self.find_alias_set(e1);
        let s2 = self.find_alias_set(e2);
        s1.is_some() && s1 == s2
    }

    #[inline(always)]
    pub fn merge_alias_sets(&mut self, e1: usize, e2: usize) {
        let mut s1 = self.find_alias_set(e1);
        let mut s2 = self.find_alias_set(e2);

        // Create set for e1 if needed
        if s1.is_none() {
            self.alias_sets
                .push([e1].into_iter().collect::<FxHashSet<usize>>());
            s1 = Some(self.alias_sets.len() - 1);
        }

        // Create set for e2 if needed
        if s2.is_none() {
            self.alias_sets
                .push([e2].into_iter().collect::<FxHashSet<usize>>());
            s2 = Some(self.alias_sets.len() - 1);
        }

        // After creation, fetch indices (unwrap OK)
        let idx1 = s1.unwrap();
        let idx2 = s2.unwrap();

        if idx1 == idx2 {
            return;
        }

        let set2 = self.alias_sets.remove(idx2);
        // If idx2 < idx1, removing idx2 shifts idx1 down by one
        let idx1 = if idx2 < idx1 { idx1 - 1 } else { idx1 };
        self.alias_sets[idx1].extend(set2);
    }

    #[inline(always)]
    pub fn get_alias_set(&mut self, e: usize) -> Option<FxHashSet<usize>> {
        if let Some(idx) = self.find_alias_set(e) {
            Some(self.alias_sets[idx].clone())
        } else {
            None
        }
    }
}
