use rustc_middle::{
    mir::{Operand, Place, ProjectionElem, TerminatorKind},
    ty::{self, TypingEnv},
};

use super::graph::*;
use crate::analysis::{
    core::alias_analysis::default::{
        MopAAFact, MopAAResultMap, assign::*, block::Term, types::*, value::*,
    },
    utils::fn_info::convert_alias_to_sets,
};

impl<'tcx> SafeDropGraph<'tcx> {
    /* alias analysis for a single block */
    pub fn alias_bb(&mut self, bb_index: usize) {
        for constant in self.mop_graph.blocks[bb_index].const_value.clone() {
            self.mop_graph
                .constants
                .insert(constant.local, constant.value);
        }
        let cur_block = self.mop_graph.blocks[bb_index].clone();
        for assign in cur_block.assignments {
            let mut lv_idx = self.projection(false, assign.lv);
            let rv_idx = self.projection(true, assign.rv);
            match assign.atype {
                AssignType::Variant => {
                    self.mop_graph.alias_set[lv_idx] = rv_idx;
                    continue;
                }
                AssignType::InitBox => {
                    lv_idx = *self.mop_graph.values[lv_idx].fields.get(&0).unwrap();
                }
                _ => {} // Copy or Move
            }
            self.fill_birth(lv_idx, self.mop_graph.blocks[bb_index].scc.enter as isize);
            if self.mop_graph.values[lv_idx].local != self.mop_graph.values[rv_idx].local {
                rap_debug!(
                    "[alias_bb] merge alias: lv_idx/local:{}/{}, rv_idx/local:{}/{}, assign_type={:?}",
                    lv_idx,
                    self.mop_graph.values[lv_idx].local,
                    rv_idx,
                    self.mop_graph.values[rv_idx].local,
                    assign.atype
                );
                self.merge_alias(lv_idx, rv_idx, 0);
                rap_debug!(
                    "Alias sets: {:?}",
                    convert_alias_to_sets(self.mop_graph.alias_set.clone())
                );
            }
            self.uaf_check(bb_index, rv_idx, assign.span, false);
        }
    }

    /* Check the aliases introduced by the terminators (function call) of a scc block */
    pub fn alias_bbcall(&mut self, bb_index: usize, fn_map: &MopAAResultMap) {
        let cur_block = self.mop_graph.blocks[bb_index].clone();
        if let Term::Call(call) | Term::Drop(call) = cur_block.terminator {
            if let TerminatorKind::Call {
                ref func,
                ref args,
                ref destination,
                target: _,
                unwind: _,
                call_source: _,
                fn_span: _,
            } = call.kind
            {
                if let Operand::Constant(constant) = func {
                    let lv = self.projection(false, destination.clone());
                    self.mop_graph.values[lv].birth =
                        self.mop_graph.blocks[bb_index].scc.enter as isize;
                    let mut merge_vec = Vec::new();
                    merge_vec.push(lv);
                    let mut may_drop_flag = 0;
                    if self.mop_graph.values[lv].may_drop {
                        may_drop_flag += 1;
                    }
                    for arg in args {
                        match arg.node {
                            Operand::Copy(ref p) => {
                                let rv = self.projection(true, p.clone());
                                //self.uaf_check(rv, call.source_info.span, p.local.as_usize(), true);
                                self.uaf_check(bb_index, rv, call.source_info.span, true);
                                merge_vec.push(rv);
                                if self.mop_graph.values[rv].may_drop {
                                    may_drop_flag += 1;
                                }
                            }
                            Operand::Move(ref p) => {
                                let rv = self.projection(true, p.clone());
                                self.uaf_check(bb_index, rv, call.source_info.span, true);
                                merge_vec.push(rv);
                                if self.mop_graph.values[rv].may_drop {
                                    may_drop_flag += 1;
                                }
                            }
                            Operand::Constant(_) => {
                                merge_vec.push(0);
                            }
                        }
                    }
                    if let ty::FnDef(target_id, _) = constant.const_.ty().kind() {
                        if may_drop_flag > 1 {
                            if self.mop_graph.tcx.is_mir_available(*target_id) {
                                if fn_map.contains_key(&target_id) {
                                    let assignments = fn_map.get(&target_id).unwrap();
                                    for assign in assignments.aliases().iter() {
                                        if !assign.valuable() {
                                            continue;
                                        }
                                        self.merge(assign, &merge_vec);
                                    }
                                }
                            } else {
                                if self.mop_graph.values[lv].may_drop {
                                    if self.corner_handle(lv, &merge_vec, *target_id) {
                                        return;
                                    }
                                    let mut right_set = Vec::new();
                                    for rv in &merge_vec {
                                        if self.mop_graph.values[*rv].may_drop
                                            && lv != *rv
                                            && self.mop_graph.values[lv].is_ptr()
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
        }
    }

    // assign to the variable _x, we will set the birth of _x and its child self.mop_graph.values a new birth.
    pub fn fill_birth(&mut self, node: usize, birth: isize) {
        self.mop_graph.values[node].birth = birth;
        for i in 0..self.mop_graph.values.len() {
            if self.mop_graph.union_is_same(i, node) && self.mop_graph.values[i].birth == -1 {
                self.mop_graph.values[i].birth = birth;
            }
        }
        for i in self.mop_graph.values[node].fields.clone().into_iter() {
            self.fill_birth(i.1, birth); //i.1 corresponds to the local field.
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
        let mut proj_id = local;
        for proj in place.projection {
            let new_id = self.mop_graph.values.len();
            match proj {
                ProjectionElem::Deref => {
                    //proj_id = self.mop_graph.values[proj_id].alias[0];
                    proj_id = self.mop_graph.alias_set[proj_id];
                }
                /*
                 * Objective: 2 = 1.0; 0 = 2.0; => 0 = 1.0.0
                 */
                ProjectionElem::Field(field, ty) => {
                    if is_right && self.mop_graph.alias_set[proj_id] != proj_id {
                        proj_id = self.mop_graph.alias_set[proj_id];
                        local = self.mop_graph.values[proj_id].local;
                    }
                    let field_idx = field.as_usize();
                    if !self.mop_graph.values[proj_id]
                        .fields
                        .contains_key(&field_idx)
                    {
                        let ty_env =
                            TypingEnv::post_analysis(self.mop_graph.tcx, self.mop_graph.def_id);
                        let need_drop = ty.needs_drop(self.mop_graph.tcx, ty_env);
                        let may_drop = !is_not_drop(self.mop_graph.tcx, ty);
                        let mut node = Value::new(new_id, local, need_drop, need_drop || may_drop);
                        node.kind = kind(ty);
                        node.birth = self.mop_graph.values[proj_id].birth;
                        node.field_id = field_idx;
                        self.mop_graph.values[proj_id]
                            .fields
                            .insert(field_idx, node.index);
                        self.mop_graph
                            .alias_set
                            .push(self.mop_graph.alias_set.len());
                        self.drop_record.push(self.drop_record[proj_id]);
                        self.mop_graph.values.push(node);
                    }
                    proj_id = *self.mop_graph.values[proj_id]
                        .fields
                        .get(&field_idx)
                        .unwrap();
                }
                _ => {}
            }
        }
        return proj_id;
    }

    //instruction to assign alias for a variable.
    pub fn merge_alias(&mut self, lv: usize, rv: usize, depth: usize) {
        if lv >= self.mop_graph.values.len() || rv >= self.mop_graph.values.len() {
            return;
        }
        self.mop_graph.union_merge(lv, rv);

        let max_field_depth = match std::env::var_os("SAFEDROP") {
            Some(val) if val == "0" => 10,
            Some(val) if val == "1" => 20,
            Some(val) if val == "2" => 30,
            Some(val) if val == "3" => 50,
            _ => 15,
        };

        if depth > max_field_depth {
            return;
        }

        for field in self.mop_graph.values[rv].fields.clone().into_iter() {
            if !self.mop_graph.values[lv].fields.contains_key(&field.0) {
                let mut node = Value::new(
                    self.mop_graph.values.len(),
                    self.mop_graph.values[lv].local,
                    self.mop_graph.values[field.1].need_drop,
                    self.mop_graph.values[field.1].may_drop,
                );
                node.kind = self.mop_graph.values[field.1].kind;
                node.birth = self.mop_graph.values[lv].birth;
                node.field_id = field.0;
                self.mop_graph.values[lv].fields.insert(field.0, node.index);
                self.mop_graph
                    .alias_set
                    .push(self.mop_graph.alias_set.len());
                self.drop_record.push(DropRecord::false_record());
                self.mop_graph.values.push(node);
            }
            let lv_field = *(self.mop_graph.values[lv].fields.get(&field.0).unwrap());
            self.merge_alias(lv_field, field.1, depth + 1);
        }
    }

    //inter-procedure instruction to merge alias.
    pub fn merge(&mut self, ret_alias: &MopAAFact, arg_vec: &Vec<usize>) {
        if ret_alias.lhs_no() >= arg_vec.len() || ret_alias.rhs_no() >= arg_vec.len() {
            rap_error!("Vector error!");
            return;
        }
        let left_init = arg_vec[ret_alias.lhs_no()];
        let mut right_init = arg_vec[ret_alias.rhs_no()];
        let mut lv = left_init;
        let mut rv = right_init;
        for index in ret_alias.lhs_fields().iter() {
            if self.mop_graph.values[lv].fields.contains_key(&index) == false {
                let need_drop = ret_alias.lhs_need_drop;
                let may_drop = ret_alias.lhs_may_drop;
                let mut node =
                    Value::new(self.mop_graph.values.len(), left_init, need_drop, may_drop);
                node.kind = TyKind::RawPtr;
                node.birth = self.mop_graph.values[lv].birth;
                node.field_id = *index;
                self.mop_graph.values[lv].fields.insert(*index, node.index);
                self.mop_graph
                    .alias_set
                    .push(self.mop_graph.alias_set.len());
                self.drop_record.push(self.drop_record[lv]);
                self.mop_graph.values.push(node);
            }
            lv = *self.mop_graph.values[lv].fields.get(&index).unwrap();
        }
        for index in ret_alias.rhs_fields().iter() {
            // if self.mop_graph.values[rv].alias[0] != rv {
            if self
                .mop_graph
                .union_is_same(rv, self.mop_graph.alias_set[rv])
            {
                rv = self.mop_graph.values[rv].index;
                right_init = self.mop_graph.values[rv].local;
            }
            if !self.mop_graph.values[rv].fields.contains_key(&index) {
                let need_drop = ret_alias.rhs_need_drop;
                let may_drop = ret_alias.rhs_may_drop;
                let mut node = Value::new(
                    self.mop_graph.alias_set.len(),
                    right_init,
                    need_drop,
                    may_drop,
                );
                node.kind = TyKind::RawPtr;
                node.birth = self.mop_graph.values[rv].birth;
                node.field_id = *index;
                self.mop_graph.values[rv].fields.insert(*index, node.index);
                self.mop_graph.alias_set.push(self.mop_graph.values.len());
                self.drop_record.push(self.drop_record[rv]);
                self.mop_graph.values.push(node);
            }
            rv = *self.mop_graph.values[rv].fields.get(&index).unwrap();
        }
        self.merge_alias(lv, rv, 0);
    }
}
