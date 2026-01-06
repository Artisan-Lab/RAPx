use super::{bug_records::TyBug, graph::*};
use crate::{analysis::core::alias_analysis::default::types::TyKind, utils::source::*};
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
        rap_debug!(
            "uaf_check, idx: {:?}, local: {:?}, drop_record: {:?}",
            idx,
            local,
            self.drop_record[idx],
        );

        if !self.mop_graph.values[idx].may_drop {
            return;
        }
        if self.mop_graph.values[idx].is_ptr() && !is_fncall {
            return;
        }

        self.sync_drop_record(idx);

        let mut fully_dropped = true;
        if !self.drop_record[idx].is_dropped {
            fully_dropped = false;
            if !self.drop_record[idx].has_dropped_field {
                return;
            }
        }

        rap_debug!(
            "is_ptr: {}, is_fn_call: {}",
            self.mop_graph.values[idx].is_ptr(),
            is_fncall
        );

        let kind = self.mop_graph.values[idx].kind;
        let confidence = Self::rate_confidence(kind, fully_dropped);

        let bug = TyBug {
            drop_info: self.drop_record[idx].drop_info,
            trigger_info: LocalSpot::new(bb_idx, local),
            span: span.clone(),
            confidence,
        };
        if self.bug_records.uaf_bugs.contains_key(&local) {
            return;
        }
        rap_warn!("Find a use-after-free bug {:?}; add to records", bug);
        self.bug_records.uaf_bugs.insert(local, bug);
    }

    pub fn rate_confidence(kind: TyKind, fully_dropped: bool) -> usize {
        let confidence = match (kind, fully_dropped) {
            (TyKind::CornerCase, _) => 0,
            (_, true) => 99,
            (_, false) => 50,
        };
        confidence
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
            for value_idx in aliases {
                // set idx as dropped if any of its alias has been dropped.
                if self.drop_record[value_idx].is_dropped {
                    self.drop_record[idx] = self.drop_record[value_idx];
                    // set has_dropped_field = true for the father and all ancestors up the chain.
                    let mut father = self.mop_graph.values[idx].father.clone();
                    while let Some(father_info) = father {
                        let father_idx = father_info.father_value_id;
                        self.drop_record[father_idx].has_dropped_field = true;
                        father = self.mop_graph.values[father_idx].father.clone();
                    }
                }
            }
        }
    }

    pub fn df_check(&mut self, bb_idx: usize, idx: usize, span: Span, flag_cleanup: bool) -> bool {
        let local = self.mop_graph.values[idx].local;
        // If the value has not been dropped, it is not a double free.
        rap_debug!(
            "df_check: bb_idx = {:?}, idx = {:?}, local = {:?}, alias_sets: {:?}",
            bb_idx,
            idx,
            local,
            self.mop_graph.alias_sets,
        );

        let mut fully_dropped = true;
        if !self.drop_record[idx].is_dropped {
            fully_dropped = false;
            if !self.drop_record[idx].has_dropped_field {
                return false;
            }
        }
        let kind = self.mop_graph.values[idx].kind;
        let confidence = Self::rate_confidence(kind, fully_dropped);

        let bug = TyBug {
            drop_info: self.drop_record[idx].drop_info,
            trigger_info: LocalSpot::new(bb_idx, local),
            span: span.clone(),
            confidence,
        };

        for item in &self.drop_record {
            rap_info!("drop_info: {:?}", item);
        }
        if flag_cleanup {
            if !self.bug_records.df_bugs_unwind.contains_key(&local) {
                self.bug_records.df_bugs_unwind.insert(local, bug);
                rap_info!(
                    "Find a double free bug {} during unwinding; add to records.",
                    local
                );
            }
        } else {
            if !self.bug_records.df_bugs.contains_key(&local) {
                self.bug_records.df_bugs.insert(local, bug);
                rap_info!("Find a double free bug {}; add to records.", local);
            }
        }
        return true;
    }

    pub fn dp_check(&mut self, flag_cleanup: bool) {
        rap_debug!("dangling pointer check");
        rap_debug!("current alias sets: {:?}", self.mop_graph.alias_sets);
        if flag_cleanup {
            for arg_idx in 1..self.mop_graph.arg_size + 1 {
                if !self.mop_graph.values[arg_idx].is_ptr() {
                    continue;
                }
                let mut fully_dropped = true;
                if !self.drop_record[arg_idx].is_dropped {
                    fully_dropped = false;
                    if !self.drop_record[arg_idx].has_dropped_field {
                        continue;
                    }
                }
                let kind = self.mop_graph.values[arg_idx].kind;
                let confidence = Self::rate_confidence(kind, fully_dropped);
                let bug = TyBug {
                    drop_info: self.drop_record[arg_idx].drop_info,
                    trigger_info: LocalSpot::from_local(arg_idx),
                    span: self.mop_graph.span.clone(),
                    confidence,
                };
                self.bug_records.dp_bugs_unwind.insert(arg_idx, bug);
                rap_info!(
                    "Find a dangling pointer {} during unwinding; add to record.",
                    arg_idx
                );
            }
        } else {
            if self.mop_graph.values[0].may_drop
                && (self.drop_record[0].is_dropped || self.drop_record[0].has_dropped_field)
            {
                let mut fully_dropped = true;
                if !self.drop_record[0].is_dropped {
                    fully_dropped = false;
                }

                let kind = self.mop_graph.values[0].kind;
                let confidence = Self::rate_confidence(kind, fully_dropped);
                let bug = TyBug {
                    drop_info: self.drop_record[0].drop_info,
                    trigger_info: LocalSpot::from_local(0),
                    span: self.mop_graph.span.clone(),
                    confidence,
                };
                self.bug_records.dp_bugs.insert(0, bug);
                rap_info!("Find a dangling pointer 0; add to record.");
            } else {
                for arg_idx in 0..self.mop_graph.arg_size + 1 {
                    if !self.mop_graph.values[arg_idx].is_ptr() {
                        continue;
                    }
                    let mut fully_dropped = true;
                    if !self.drop_record[arg_idx].is_dropped {
                        fully_dropped = false;
                        if !self.drop_record[arg_idx].has_dropped_field {
                            continue;
                        }
                    }
                    let kind = self.mop_graph.values[arg_idx].kind;
                    let confidence = Self::rate_confidence(kind, fully_dropped);
                    let bug = TyBug {
                        drop_info: self.drop_record[arg_idx].drop_info,
                        trigger_info: LocalSpot::from_local(arg_idx),
                        span: self.mop_graph.span.clone(),
                        confidence,
                    };
                    self.bug_records.dp_bugs.insert(arg_idx, bug);
                    rap_info!("Find a dangling pointer {}; add to record.", arg_idx);
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
            let drop_info = LocalSpot::new(bb_idx, self.mop_graph.values[via_idx].local);
            self.drop_record[idx] = DropRecord::new(idx, true, drop_info);
            rap_debug!(
                "add_to_drop_record: idx = {}, {:?}",
                idx,
                self.drop_record[idx]
            );
            // sync the father node: has_dropped_field
            let mut father = self.mop_graph.values[idx].father.clone();
            while let Some(father_info) = father {
                let father_idx = father_info.father_value_id;
                self.drop_record[father_idx].has_dropped_field = true;
                father = self.mop_graph.values[father_idx].father.clone();
            }
            //drop the fields of the root node.
            for (_field_id, field_value_id) in self.mop_graph.values[idx].fields.clone() {
                if self.mop_graph.values[idx].is_tuple()
                    && !self.mop_graph.values[field_value_id].need_drop
                {
                    continue;
                }
                self.add_to_drop_record(
                    field_value_id,
                    self.mop_graph.values[via_idx].local,
                    info,
                    false,
                    bb_idx,
                    flag_cleanup,
                );
            }
        }
        if !flag_inprocess {
            //drop their alias
            if let Some(aliases) = self.mop_graph.get_alias_set(idx) {
                for i in aliases {
                    self.add_to_drop_record(
                        i,
                        self.mop_graph.values[via_idx].local,
                        info,
                        true,
                        bb_idx,
                        flag_cleanup,
                    );
                }
            }
        }
    }
}
