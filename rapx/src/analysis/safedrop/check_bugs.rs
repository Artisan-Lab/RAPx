use super::{bug_records::TyBug, graph::*};
use crate::{
    analysis::core::alias_analysis::default::{types::TyKind, value::*},
    utils::source::*,
};
use rustc_middle::mir::SourceInfo;
use rustc_span::{Span, symbol::Symbol};

impl<'tcx> SafeDropGraph<'tcx> {
    pub fn report_bugs(&self) {
        rap_debug!(
            "report bugs, id: {:?}, uaf: {:?}",
            self.mop_graph.def_id,
            self.bug_records.uaf_bugs
        );
        let filename = get_filename(self.mop_graph.tcx, self.mop_graph.def_id);
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
        let fn_name = match get_name(self.mop_graph.tcx, self.mop_graph.def_id) {
            Some(name) => name,
            None => Symbol::intern("no symbol available"),
        };
        let body = self.mop_graph.tcx.optimized_mir(self.mop_graph.def_id);
        self.bug_records
            .df_bugs_output(body, fn_name, self.mop_graph.span);
        self.bug_records
            .uaf_bugs_output(body, fn_name, self.mop_graph.span);
        self.bug_records
            .dp_bug_output(body, fn_name, self.mop_graph.span);
        /*
        let _ = generate_mir_cfg_dot(
            self.mop_graph.tcx,
            self.mop_graph.def_id,
            &self.mop_graph.alias_sets,
        );
        */
    }

    pub fn uaf_check(&mut self, bb_idx: usize, idx: usize, span: Span, is_fncall: bool) {
        let local = self.mop_graph.values[idx].local;
        if !self.mop_graph.values[idx].may_drop {
            return;
        }
        rap_debug!(
            "uaf_check, idx: {:?}, local: {:?}, drop_record: {:?}, local_drop_record: {:?}",
            idx,
            local,
            self.drop_record[idx],
            self.drop_record[local],
        );

        self.sync_drop_record(idx);
        rap_debug!(
            "after sync drop record: idx: {:?}, local: {:?}, drop_record: {:?}",
            idx,
            local,
            self.drop_record[idx]
        );
        if !self.drop_record[idx].is_dropped {
            return;
        }
        rap_debug!(
            "is_ptr: {}, is_fn_call: {}",
            self.mop_graph.values[idx].is_ptr(),
            is_fncall
        );
        if self.mop_graph.values[idx].is_ptr() && !is_fncall {
            return;
        }

        let confidence = match self.mop_graph.values[idx].kind {
            TyKind::CornerCase => 0,
            _ => 99,
        };

        let bug = TyBug {
            drop_bb: self.drop_record[idx].drop_at_bb,
            drop_id: self.drop_record[idx].drop_via_local,
            trigger_bb: bb_idx,
            trigger_id: local,
            span: span.clone(),
            confidence,
        };
        if self.bug_records.uaf_bugs.contains_key(&local) {
            return;
        }
        rap_warn!("Find use-after-free bug {:?}; add to records", bug);
        self.bug_records.uaf_bugs.insert(local, bug);
    }

    pub fn sync_drop_record(&mut self, idx: usize) {
        if idx >= self.mop_graph.values.len() {
            return;
        }
        let local = self.mop_graph.values[idx].local;
        if self.drop_record[local].is_dropped {
            self.drop_record[idx] = self.drop_record[local];
        }
        if let Some(aliases) = self.mop_graph.get_alias_set(local) {
            for i in aliases.iter() {
                if self.drop_record[*i].is_dropped {
                    self.drop_record[idx] = self.drop_record[*i];
                    return;
                }
            }
        }
    }

    pub fn df_check(&mut self, bb_idx: usize, idx: usize, span: Span, flag_cleanup: bool) -> bool {
        let local = self.mop_graph.values[idx].local;
        // If the value has not been dropped, it is not a double free.
        rap_debug!(
            "df_check: bb_idx = {:?}, idx = {:?}, local = {:?}",
            bb_idx,
            idx,
            local
        );
        rap_debug!(
            "df_check: is alive? {:?}",
            self.mop_graph.values[idx].is_alive()
        );
        if self.mop_graph.values[idx].is_alive() {
            return false;
        }
        let confidence = match self.mop_graph.values[idx].kind {
            TyKind::CornerCase => 0,
            _ => 99,
        };
        let bug = TyBug {
            drop_bb: self.drop_record[idx].drop_at_bb,
            drop_id: self.drop_record[idx].drop_via_local,
            trigger_bb: bb_idx,
            trigger_id: local,
            span: span.clone(),
            confidence,
        };

        if flag_cleanup {
            if !self.bug_records.df_bugs_unwind.contains_key(&local) {
                self.bug_records.df_bugs_unwind.insert(local, bug);
                rap_warn!(
                    "Find double free bug {} during unwinding; add to records.",
                    local
                );
            }
        } else {
            if !self.bug_records.df_bugs.contains_key(&local) {
                self.bug_records.df_bugs.insert(local, bug);
                rap_warn!("Find double free bug {}; add to records.", local);
            }
        }
        return true;
    }

    pub fn dp_check(&mut self, flag_cleanup: bool) {
        if flag_cleanup {
            for arg_idx in 1..self.mop_graph.arg_size + 1 {
                if self.mop_graph.values[arg_idx].is_ptr() && self.drop_record[arg_idx].is_dropped {
                    let confidence = match self.mop_graph.values[arg_idx].kind {
                        TyKind::CornerCase => 0,
                        _ => 99,
                    };
                    let bug = TyBug {
                        drop_bb: self.drop_record[arg_idx].drop_at_bb,
                        drop_id: self.drop_record[arg_idx].drop_via_local,
                        trigger_bb: usize::MAX,
                        trigger_id: arg_idx,
                        span: self.mop_graph.span.clone(),
                        confidence,
                    };
                    self.bug_records.dp_bugs_unwind.insert(arg_idx, bug);
                    rap_warn!(
                        "Find dangling pointer {} during unwinding; add to record.",
                        arg_idx
                    );
                }
            }
        } else {
            if self.mop_graph.values[0].may_drop && self.drop_record[0].is_dropped {
                let confidence = match self.mop_graph.values[0].kind {
                    TyKind::CornerCase => 0,
                    _ => 99,
                };
                let bug = TyBug {
                    drop_bb: self.drop_record[0].drop_at_bb,
                    drop_id: self.drop_record[0].drop_via_local,
                    trigger_bb: usize::MAX,
                    trigger_id: 0,
                    span: self.mop_graph.span.clone(),
                    confidence,
                };
                self.bug_records.dp_bugs.insert(0, bug);
                rap_warn!("Find dangling pointer 0; add to record.");
            } else {
                for arg_idx in 0..self.mop_graph.arg_size + 1 {
                    if self.mop_graph.values[arg_idx].is_ptr()
                        && self.drop_record[arg_idx].is_dropped
                    {
                        let confidence = match self.mop_graph.values[arg_idx].kind {
                            TyKind::CornerCase => 0,
                            _ => 99,
                        };
                        let bug = TyBug {
                            drop_bb: self.drop_record[arg_idx].drop_at_bb,
                            drop_id: self.drop_record[arg_idx].drop_via_local,
                            trigger_bb: usize::MAX,
                            trigger_id: arg_idx,
                            span: self.mop_graph.span.clone(),
                            confidence,
                        };
                        self.bug_records.dp_bugs.insert(arg_idx, bug);
                        rap_warn!("Find dangling pointer {}; add to record.", arg_idx);
                    }
                }
            }
        }
    }

    /*
     * Mark the node as dropped.
     * flag_cleanup: used to distinguish if a bug occurs in the unwinding path.
     */
    pub fn add_to_drop_record(
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
        if self.mop_graph.values[idx].is_corner_case() {
            return;
        }
        //check if there is a double free bug.
        if !flag_inprocess && self.df_check(bb_idx, idx, self.mop_graph.span, flag_cleanup) {
            return;
        }
        if !self.drop_record[idx].is_dropped {
            self.drop_record[idx] =
                DropRecord::new(true, bb_idx, self.mop_graph.values[via_idx].local);
            rap_debug!(
                "add_to_drop_record: idx = {}, {:?}",
                idx,
                self.drop_record[idx]
            );
            //drop their alias
            for i in 0..self.mop_graph.values.len() {
                if !self.mop_graph.is_aliasing(idx, i)
                    || i == idx
                    || self.mop_graph.values[i].is_ref()
                {
                    continue;
                }
                self.add_to_drop_record(
                    i,
                    self.mop_graph.values[via_idx].local,
                    birth,
                    info,
                    true,
                    bb_idx,
                    flag_cleanup,
                );
            }
        } else {
            return;
        }
        //drop the fields of the root node.
        //alias flag is used to avoid the fields of the alias are dropped repeatly.
        if !flag_inprocess {
            for (_, field_idx) in self.mop_graph.values[idx].fields.clone() {
                if self.mop_graph.values[idx].is_tuple()
                    && !self.mop_graph.values[field_idx].need_drop
                {
                    continue;
                }
                self.add_to_drop_record(
                    field_idx,
                    self.mop_graph.values[via_idx].local,
                    birth,
                    info,
                    true,
                    bb_idx,
                    flag_cleanup,
                );
            }
        }
        //SCC.
        if self.mop_graph.values[idx].birth < birth as isize && self.mop_graph.values[idx].may_drop
        {
            self.mop_graph.values[idx].drop();
        }
    }

    pub fn get_field_seq(&self, value: &Value) -> Vec<usize> {
        let mut field_id_seq = vec![];
        let mut node_ref = value;
        while node_ref.field_id != usize::MAX {
            field_id_seq.push(node_ref.field_id);
            node_ref = &self.mop_graph.values[value.father];
        }
        return field_id_seq;
    }
}
