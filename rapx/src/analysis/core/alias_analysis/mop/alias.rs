use super::graph::*;
use super::types::*;
use crate::{
    analysis::{
        core::alias_analysis::mop::{FnMap, MopAAFact},
        utils::intrinsic_id::*,
    },
    rap_debug,
};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Operand, Place, ProjectionElem, TerminatorKind},
    ty,
};
use std::collections::HashSet;

impl<'tcx> MopGraph<'tcx> {
    /* alias analysis for a single block */
    pub fn alias_bb(&mut self, bb_index: usize) {
        for stmt in self.blocks[bb_index].const_value.clone() {
            self.constant.insert(stmt.0, stmt.1);
        }
        let cur_block = self.blocks[bb_index].clone();
        for assign in cur_block.assignments {
            let mut lv_aliaset_idx = self.projection(false, assign.lv);
            let rv_aliaset_idx = self.projection(true, assign.rv);
            rap_debug!("{:?} = {:?}", lv_aliaset_idx, rv_aliaset_idx);
            match assign.atype {
                AssignType::Variant => {
                    self.alias_set[lv_aliaset_idx] = rv_aliaset_idx;
                    continue;
                }
                AssignType::InitBox => {
                    lv_aliaset_idx = *self.values[lv_aliaset_idx].fields.get(&0).unwrap();
                }
                _ => {} // Copy or Move
            }
            if self.values[lv_aliaset_idx].local != self.values[rv_aliaset_idx].local {
                self.merge_alias(lv_aliaset_idx, rv_aliaset_idx, 0);
            }
        }
    }

    /* Check the aliases introduced by the terminators (function call) of a scc block */
    pub fn alias_bbcall(
        &mut self,
        bb_index: usize,
        fn_map: &mut FnMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        let cur_block = self.blocks[bb_index].clone();
        for call in cur_block.calls {
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
                let lv = self.projection(false, *destination);
                let mut merge_vec = Vec::new();
                merge_vec.push(lv);
                let mut may_drop_flag = 0;
                if self.values[lv].may_drop {
                    may_drop_flag += 1;
                }
                for arg in args {
                    match arg.node {
                        Operand::Copy(ref p) => {
                            let rv = self.projection(true, *p);
                            merge_vec.push(rv);
                            if self.values[rv].may_drop {
                                may_drop_flag += 1;
                            }
                        }
                        Operand::Move(ref p) => {
                            let rv = self.projection(true, *p);
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
                if let ty::FnDef(ref target_id, _) = constant.const_.ty().kind() {
                    //if may_drop_flag > 1 || Self::should_check(target_id.clone()) == false {
                    if may_drop_flag > 0 {
                        if self.tcx.is_mir_available(*target_id) {
                            rap_debug!("target_id {:?}", target_id);
                            if fn_map.contains_key(target_id) {
                                let assignments = fn_map.get(target_id).unwrap();
                                for assign in assignments.aliases().iter() {
                                    if !assign.valuable() {
                                        continue;
                                    }
                                    self.merge(assign, &merge_vec);
                                }
                            } else {
                                /* Fixed-point iteration: this is not perfect */
                                if recursion_set.contains(target_id) {
                                    continue;
                                }
                                recursion_set.insert(*target_id);
                                let mut mop_graph = MopGraph::new(self.tcx, *target_id);
                                mop_graph.solve_scc();
                                mop_graph.check(0, fn_map, recursion_set);
                                let ret_alias = mop_graph.ret_alias.clone();
                                for assign in ret_alias.aliases().iter() {
                                    if !assign.valuable() {
                                        continue;
                                    }
                                    self.merge(assign, &merge_vec);
                                }
                                fn_map.insert(*target_id, ret_alias);
                                recursion_set.remove(target_id);
                            }
                        } else if self.values[lv].may_drop {
                            if target_id.index.as_usize() == CALL_MUT {
                                continue;
                            }

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
                                self.merge_alias(lv, right_set[0], 0);
                            }
                        }
                    }
                }
            }
        }
    }

    /*
     * This is the function for field sensitivity
     * If the projection is a deref, we directly return its head alias or alias[0].
     * If the id is not a ref, we further make the id and its first element an alias, i.e., level-insensitive
     *
     */
    pub fn projection(&mut self, is_right: bool, place: Place<'tcx>) -> usize {
        let mut local = place.local.as_usize();
        let mut proj_id: usize = local;
        for proj in place.projection {
            let new_id = self.values.len();
            match proj {
                ProjectionElem::Deref => {
                    proj_id = self.values[proj_id].index;
                }
                /*
                 * Objective: 2 = 1.0; 0 = 2.0; => 0 = 1.0.0
                 */
                ProjectionElem::Field(field, ty) => {
                    if is_right && self.values[proj_id].index != proj_id {
                        proj_id = self.values[proj_id].index;
                        local = self.values[proj_id].local;
                    }
                    let field_idx = field.as_usize();
                    if let std::collections::hash_map::Entry::Vacant(e) =
                        self.values[proj_id].fields.entry(field_idx)
                    {
                        let ty_env = ty::TypingEnv::post_analysis(self.tcx, self.def_id);
                        let need_drop = ty.needs_drop(self.tcx, ty_env);
                        let may_drop = !is_not_drop(self.tcx, ty);
                        let mut node =
                            ValueNode::new(new_id, local, need_drop, need_drop || may_drop);
                        node.kind = kind(ty);
                        node.field_id = field_idx;
                        e.insert(node.index);
                        self.alias_set.push(self.values.len());
                        self.values.push(node);
                    }
                    proj_id = *self.values[proj_id].fields.get(&field_idx).unwrap();
                }
                _ => {}
            }
        }
        proj_id
    }

    //assign alias for a variable.
    pub fn merge_alias(&mut self, lv: usize, rv: usize, depth: usize) {
        rap_debug!("Alias set before merge: {:?}", self.alias_set);
        // println!("A:{:?} V:{:?}", self.alias_set, self.values.len());
        self.union_merge(lv, rv);
        // println!("Li:{} Ri:{} L:{:?} R:{:?} A:{:?} V:{:?}", self.values[lv].index, self.values[rv].index, self.values[lv].alias ,self.values[rv].alias, self.alias_set, self.values.len());
        rap_debug!(
            "update the alias set for lv:{} rv:{} set:{:?}",
            lv,
            rv,
            self.alias_set
        );

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

        for field in self.values[rv].fields.clone().into_iter() {
            if !self.values[lv].fields.contains_key(&field.0) {
                let mut node = ValueNode::new(
                    self.values.len(),
                    self.values[lv].local,
                    self.values[field.1].need_drop,
                    self.values[field.1].may_drop,
                );
                node.kind = self.values[field.1].kind;
                node.field_id = field.0;
                self.values[lv].fields.insert(field.0, node.index);
                self.alias_set.push(self.values.len());
                self.values.push(node);
            }
            let lv_field = *(self.values[lv].fields.get(&field.0).unwrap());
            self.merge_alias(lv_field, field.1, depth + 1);
        }
    }

    //inter-procedure instruction to merge alias.
    pub fn merge(&mut self, ret_alias: &MopAAFact, arg_vec: &[usize]) {
        rap_debug!("{:?}", ret_alias);
        if ret_alias.lhs_no() >= arg_vec.len() || ret_alias.rhs_no() >= arg_vec.len() {
            rap_debug!("Vector error!");
            return;
        }
        let left_init = arg_vec[ret_alias.lhs_no()];
        let mut right_init = arg_vec[ret_alias.rhs_no()];
        let mut lv = left_init;
        let mut rv = right_init;
        for index in ret_alias.lhs_fields().iter() {
            if !self.values[lv].fields.contains_key(index) {
                let need_drop = ret_alias.lhs_need_drop;
                let may_drop = ret_alias.lhs_may_drop;
                let mut node = ValueNode::new(self.values.len(), left_init, need_drop, may_drop);
                node.kind = TyKind::RawPtr;
                node.field_id = *index;
                self.values[lv].fields.insert(*index, node.index);
                self.alias_set.push(self.values.len());
                self.values.push(node);
            }
            lv = *self.values[lv].fields.get(index).unwrap();
        }
        for index in ret_alias.rhs_fields().iter() {
            if self.union_is_same(rv, self.alias_set[rv]) {
                right_init = self.values[rv].local;
            }
            if !self.values[rv].fields.contains_key(index) {
                let need_drop = ret_alias.rhs_need_drop;
                let may_drop = ret_alias.rhs_may_drop;
                let mut node = ValueNode::new(self.values.len(), right_init, need_drop, may_drop);
                node.kind = TyKind::RawPtr;
                node.field_id = *index;
                self.values[rv].fields.insert(*index, node.index);
                self.alias_set.push(self.values.len());
                self.values.push(node);
            }
            rv = *self.values[rv].fields.get(index).unwrap();
        }
        self.merge_alias(lv, rv, 0);
    }

    //merge the result of current path to the final result.
    pub fn merge_results(&mut self, results_nodes: Vec<ValueNode>) {
        for node in results_nodes.iter() {
            if node.local <= self.arg_size
                && (self.union_is_same(node.index, self.alias_set[node.index])
                    || self.alias_set[node.index] != node.index)
            {
                if self.values.len() == 1 {
                    return;
                }
                let f_node: Vec<usize> = results_nodes.iter().map(|v| v.father).collect();

                for idx in 1..self.values.len() {
                    if !self.union_is_same(idx, node.index) {
                        continue;
                    }

                    let mut replace = None;
                    if results_nodes[idx].local > self.arg_size {
                        for (i, &fidx) in f_node.iter().enumerate() {
                            if i != idx && i != node.index && fidx == f_node[idx] {
                                for (j, v) in results_nodes.iter().enumerate() {
                                    if j != idx
                                        && j != node.index
                                        && self.union_is_same(j, fidx)
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
                        self.ret_alias.add_alias(new_alias);
                    }
                }
            }
        }
    }

    pub fn get_field_seq(&self, value: &ValueNode) -> Vec<usize> {
        let mut field_id_seq = vec![];
        let mut node_ref = value;
        while node_ref.field_id != usize::MAX {
            field_id_seq.push(node_ref.field_id);
            node_ref = &self.values[value.father];
        }
        field_id_seq
    }

    #[inline]
    pub fn union_find(&mut self, e: usize) -> usize {
        let mut r = e;
        while self.alias_set[r] != r {
            r = self.alias_set[r];
        }
        r
    }

    #[inline]
    pub fn union_merge(&mut self, e1: usize, e2: usize) {
        let f1 = self.union_find(e1);
        let f2 = self.union_find(e2);

        if f1 < f2 {
            self.alias_set[f2] = f1;
        }
        if f1 > f2 {
            self.alias_set[f1] = f2;
        }

        for member in 0..self.alias_set.len() {
            self.alias_set[member] = self.union_find(self.alias_set[member]);
        }
    }

    #[inline]
    pub fn union_is_same(&mut self, e1: usize, e2: usize) -> bool {
        let f1 = self.union_find(e1);
        let f2 = self.union_find(e2);
        f1 == f2
    }
}
