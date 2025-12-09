use super::{bug_records::TyBug, graph::*};
use crate::{
    analysis::{
        core::alias_analysis::default::{types::TyKind, value::*},
        utils::fn_info::{convert_alias_to_sets, generate_mir_cfg_dot},
    },
    utils::source::*,
};
use rustc_data_structures::fx::FxHashSet;
use rustc_middle::mir::SourceInfo;
use rustc_span::{Span, symbol::Symbol};

impl<'tcx> SafeDropGraph<'tcx> {
    pub fn report_bugs(&self) {
        let filename = get_filename(self.tcx, self.def_id);
        match filename {
            Some(filename) => {
                if filename.contains(".cargo") {
                    return;
                }
            }
            None => {}
        }
        if self.bug_records.is_bug_free() {
            return;
        }
        let fn_name = match get_name(self.tcx, self.def_id) {
            Some(name) => name,
            None => Symbol::intern("no symbol available"),
        };
        self.bug_records.df_bugs_output(fn_name, self.span);
        self.bug_records.uaf_bugs_output(fn_name, self.span);
        self.bug_records.dp_bug_output(fn_name, self.span);
        let _ = generate_mir_cfg_dot(self.tcx, self.def_id);
        rap_debug!("Alias: {:?}", convert_alias_to_sets(self.alias_set.clone()));
    }

    pub fn uaf_check(&mut self, bb_idx: usize, idx: usize, span: Span, is_func_call: bool) {
        let local = self.values[idx].local;
        if !self.values[idx].may_drop {
            return;
        }
        /*
         * Check
         * 1) if the birth of the value > -1;
         * 2) there is a drop_record entry.
         * */
        if !self.is_dangling(idx) || !self.drop_record[idx].0 {
            return;
        }
        if self.values[idx].is_ptr() && !is_func_call {
            return;
        }

        let confidence = match self.values[idx].kind {
            TyKind::CornerCase => 0,
            _ => 99,
        };

        let bug = TyBug {
            drop_bb: self.drop_record[idx].1,
            drop_id: self.drop_record[idx].2,
            trigger_bb: bb_idx,
            trigger_id: local,
            span: span.clone(),
            confidence,
        };
        rap_debug!("Find use-after-free bug {:?}; add to records", bug);
        if self.bug_records.uaf_bugs.contains_key(&local) {
            return;
        }
        self.bug_records.uaf_bugs.insert(local, bug);
        rap_debug!("Find use-after-free bug {:?}; add to records", local);
    }

    pub fn is_dangling(&mut self, local: usize) -> bool {
        let mut record = FxHashSet::default();
        return self.is_dangling_inner(local, &mut record);
    }

    fn is_dangling_inner(&mut self, idx: usize, record: &mut FxHashSet<usize>) -> bool {
        if idx >= self.values.len() {
            return false;
        }
        //if is a dangling pointer check, only check the pointer type varible.
        if self.values[idx].is_dropped() && (idx != 0 || (idx == 0 && self.values[idx].is_ptr())) {
            return true;
        }
        record.insert(idx);
        if self.union_has_alias(idx) {
            for i in 0..self.alias_set.len() {
                if i != idx && !self.union_is_same(i, idx) {
                    continue;
                }
                if record.contains(&i) == false && self.is_dangling_inner(i, record) {
                    let local = self.values[i].local;
                    if self.drop_record[local].0 {
                        rap_debug!(
                            "is_dangling_inner: idx={}, i={}, {:?}",
                            idx,
                            local,
                            self.drop_record[local]
                        );
                        self.drop_record[idx] = self.drop_record[local];
                        return true;
                    }
                }
            }
        }
        for i in self.values[idx].fields.clone().into_iter() {
            if record.contains(&i.1) == false && self.is_dangling_inner(i.1, record) {
                return true;
            }
        }
        return false;
    }

    pub fn df_check(&mut self, bb_idx: usize, idx: usize, span: Span, flag_cleanup: bool) -> bool {
        let local = self.values[idx].local;
        if !self.values[idx].is_dropped() {
            return false;
        }
        let confidence = match self.values[idx].kind {
            TyKind::CornerCase => 0,
            _ => 99,
        };
        let bug = TyBug {
            drop_bb: self.drop_record[idx].1,
            drop_id: self.drop_record[idx].2,
            trigger_bb: bb_idx,
            trigger_id: local,
            span: span.clone(),
            confidence,
        };

        if flag_cleanup {
            if !self.bug_records.df_bugs_unwind.contains_key(&local) {
                self.bug_records.df_bugs_unwind.insert(local, bug);
                rap_debug!(
                    "Find double free bug {} during unwinding; add to records.",
                    local
                );
            }
        } else {
            if !self.bug_records.df_bugs.contains_key(&local) {
                self.bug_records.df_bugs.insert(local, bug);
                rap_debug!("Find double free bug {}; add to records.", local);
            }
        }
        return true;
    }

    pub fn dp_check(&mut self, flag_cleanup: bool) {
        if flag_cleanup {
            for arg_idx in 1..self.arg_size + 1 {
                if self.values[arg_idx].is_ptr() && self.is_dangling(arg_idx) {
                    let confidence = match self.values[arg_idx].kind {
                        TyKind::CornerCase => 0,
                        _ => 99,
                    };
                    let bug = TyBug {
                        drop_bb: self.drop_record[arg_idx].1,
                        drop_id: self.drop_record[arg_idx].2,
                        trigger_bb: usize::MAX,
                        trigger_id: arg_idx,
                        span: self.span.clone(),
                        confidence,
                    };
                    self.bug_records.dp_bugs_unwind.insert(arg_idx, bug);
                    rap_debug!(
                        "Find dangling pointer {} during unwinding; add to record.",
                        arg_idx
                    );
                }
            }
        } else {
            if self.values[0].may_drop && self.is_dangling(0) {
                let confidence = match self.values[0].kind {
                    TyKind::CornerCase => 0,
                    _ => 99,
                };
                let bug = TyBug {
                    drop_bb: self.drop_record[0].1,
                    drop_id: self.drop_record[0].2,
                    trigger_bb: usize::MAX,
                    trigger_id: 0,
                    span: self.span.clone(),
                    confidence,
                };
                self.bug_records.dp_bugs.insert(0, bug);
                rap_debug!("Find dangling pointer 0; add to record.");
            } else {
                for arg_idx in 0..self.arg_size + 1 {
                    if self.values[arg_idx].is_ptr() && self.is_dangling(arg_idx) {
                        let confidence = match self.values[arg_idx].kind {
                            TyKind::CornerCase => 0,
                            _ => 99,
                        };
                        let bug = TyBug {
                            drop_bb: self.drop_record[arg_idx].1,
                            drop_id: self.drop_record[arg_idx].2,
                            trigger_bb: usize::MAX,
                            trigger_id: arg_idx,
                            span: self.span.clone(),
                            confidence,
                        };
                        self.bug_records.dp_bugs.insert(arg_idx, bug);
                        rap_debug!("Find dangling pointer {}; add to record.", arg_idx);
                    }
                }
            }
        }
    }

    /*
     * Mark the node as dropped.
     * flag_cleanup: used to distinguish if a bug occurs in the unwinding path.
     */
    pub fn drop_node(
        &mut self,
        idx: usize,     // the value to be dropped
        via_idx: usize, // the value is dropped via its alias: via_idx
        birth: usize,
        info: &SourceInfo,
        flag_inprocess: bool,
        bb_idx: usize,
        flag_cleanup: bool,
    ) {
        //Rc drop
        if self.values[idx].is_corner_case() {
            return;
        }
        //check if there is a double free bug.
        if !flag_inprocess && self.df_check(bb_idx, idx, self.span, flag_cleanup) {
            return;
        }
        let (flag_dropped, _, _) = self.drop_record[idx];
        if flag_dropped {
            return;
        } else {
            self.drop_record[idx] = (true, bb_idx, self.values[via_idx].local);
        }
        //drop their alias
        if self.alias_set[idx] != idx {
            for i in 0..self.values.len() {
                if !self.union_is_same(idx, i) || i == idx || self.values[i].is_ref() {
                    continue;
                }
                self.drop_node(
                    i,
                    self.values[via_idx].local,
                    birth,
                    info,
                    true,
                    bb_idx,
                    flag_cleanup,
                );
            }
        }
        //drop the fields of the root node.
        //alias flag is used to avoid the fields of the alias are dropped repeatly.
        if !flag_inprocess {
            for (_, field_idx) in self.values[idx].fields.clone() {
                if self.values[idx].is_tuple() && !self.values[field_idx].need_drop {
                    continue;
                }
                self.drop_node(
                    field_idx,
                    self.values[via_idx].local,
                    birth,
                    info,
                    false,
                    bb_idx,
                    flag_cleanup,
                );
            }
        }
        //SCC.
        if self.values[idx].birth < birth as isize && self.values[idx].may_drop {
            self.values[idx].drop();
        }
    }

    pub fn get_field_seq(&self, value: &ValueNode) -> Vec<usize> {
        let mut field_id_seq = vec![];
        let mut node_ref = value;
        while node_ref.field_id != usize::MAX {
            field_id_seq.push(node_ref.field_id);
            node_ref = &self.values[value.father];
        }
        return field_id_seq;
    }
}
