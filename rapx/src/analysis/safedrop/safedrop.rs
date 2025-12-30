use super::{corner_case::*, graph::*};
use crate::analysis::core::alias_analysis::default::{MopAAResultMap, block::Term};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{
        Operand::{self, Constant, Copy, Move},
        Place, TerminatorKind,
    },
    ty::{TyKind, TypingEnv},
};

pub const VISIT_LIMIT: usize = 1000;

impl<'tcx> SafeDropGraph<'tcx> {
    // analyze the drop statement and update the liveness for nodes.
    pub fn drop_check(&mut self, bb_idx: usize) {
        let cur_block = self.mop_graph.blocks[bb_idx].clone();
        let is_cleanup = cur_block.is_cleanup;
        if let Term::Drop(drop) = cur_block.terminator {
            rap_debug!("drop check bb: {}, {:?}", bb_idx, drop);
            match drop.kind {
                TerminatorKind::Drop {
                    ref place,
                    target: _,
                    unwind: _,
                    replace: _,
                    drop: _,
                    async_fut: _,
                } => {
                    if !self.drop_heap_item_check(place) {
                        return;
                    }
                    let birth = self.mop_graph.blocks[bb_idx].scc.enter;
                    let value_idx = self.projection(place.clone());
                    let info = drop.source_info.clone();
                    self.add_to_drop_record(
                        value_idx, value_idx, birth, &info, false, bb_idx, is_cleanup,
                    );
                }
                TerminatorKind::Call {
                    func: _, ref args, ..
                } => {
                    if args.len() > 0 {
                        let birth = self.mop_graph.blocks[bb_idx].scc.enter;
                        let place = match args[0].node {
                            Operand::Copy(place) => place,
                            Operand::Move(place) => place,
                            _ => {
                                rap_error!("Constant operand exists: {:?}", args[0]);
                                return;
                            }
                        };
                        if !self.drop_heap_item_check(&place) {
                            return;
                        }
                        let local = self.projection(place.clone());
                        let info = drop.source_info.clone();
                        self.add_to_drop_record(
                            local, local, birth, &info, false, bb_idx, is_cleanup,
                        );
                    }
                }
                _ => {}
            }
        }
    }

    pub fn drop_heap_item_check(&self, place: &Place<'tcx>) -> bool {
        let tcx = self.mop_graph.tcx;
        let place_ty = place.ty(&tcx.optimized_mir(self.mop_graph.def_id).local_decls, tcx);
        match place_ty.ty.kind() {
            TyKind::Adt(adtdef, ..) => match self.adt_owner.get(&adtdef.did()) {
                None => true,
                Some(owenr_unit) => {
                    let idx = match place_ty.variant_index {
                        Some(vdx) => vdx.index(),
                        None => 0,
                    };
                    if owenr_unit[idx].0.is_onheap() || owenr_unit[idx].1.contains(&true) {
                        true
                    } else {
                        false
                    }
                }
            },
            _ => true,
        }
    }

    pub fn split_check(&mut self, bb_idx: usize, fn_map: &MopAAResultMap) {
        /* duplicate the status before visiteding a path; */
        let backup_values = self.mop_graph.values.clone(); // duplicate the status when visiteding different paths;
        let backup_constant = self.mop_graph.constants.clone();
        let backup_alias_sets = self.mop_graph.alias_sets.clone();
        let backup_drop_record = self.drop_record.clone();
        self.check(bb_idx, fn_map);
        /* restore after visited */
        self.mop_graph.values = backup_values;
        self.mop_graph.constants = backup_constant;
        self.mop_graph.alias_sets = backup_alias_sets;
        self.drop_record = backup_drop_record;
    }

    pub fn split_check_with_cond(
        &mut self,
        bb_idx: usize,
        path_discr_id: usize,
        path_discr_val: usize,
        fn_map: &MopAAResultMap,
    ) {
        /* duplicate the status before visiteding a path; */
        let backup_values = self.mop_graph.values.clone(); // duplicate the status when visiteding different paths;
        let backup_constant = self.mop_graph.constants.clone();
        let backup_alias_sets = self.mop_graph.alias_sets.clone();
        let backup_drop_record = self.drop_record.clone();
        /* add control-sensitive indicator to the path status */
        self.mop_graph
            .constants
            .insert(path_discr_id, path_discr_val);
        self.check(bb_idx, fn_map);
        /* restore after visited */
        self.mop_graph.values = backup_values;
        self.mop_graph.constants = backup_constant;
        self.mop_graph.alias_sets = backup_alias_sets;
        self.drop_record = backup_drop_record;
    }

    // the core function of the safedrop.
    pub fn check(&mut self, bb_idx: usize, fn_map: &MopAAResultMap) {
        self.mop_graph.visit_times += 1;
        if self.mop_graph.visit_times > VISIT_LIMIT {
            return;
        }
        let scc_idx = self.mop_graph.blocks[bb_idx].scc.enter;
        let cur_block = self.mop_graph.blocks[bb_idx].clone();
        rap_debug!(
            "Checking bb: {}, scc_idx: {}, scc: {:?}",
            bb_idx,
            scc_idx,
            cur_block.scc.clone(),
        );

        if bb_idx == scc_idx && !cur_block.scc.nodes.is_empty() {
            rap_debug!("check {:?} as a scc", bb_idx);
            self.check_scc(bb_idx, fn_map);
        } else {
            self.check_single_node(bb_idx, fn_map);
            self.handle_nexts(bb_idx, fn_map, None, None);
        }
    }

    pub fn check_scc(&mut self, bb_idx: usize, fn_map: &MopAAResultMap) {
        let cur_block = self.mop_graph.blocks[bb_idx].clone();
        /* Handle cases if the current block is a merged scc block with sub block */
        let scc_tree = self.mop_graph.sort_scc_tree(&cur_block.scc);
        let paths_in_scc =
            self.mop_graph
                .find_scc_paths(bb_idx, &scc_tree, &mut FxHashMap::default());
        rap_debug!("Paths in scc: {:?}", paths_in_scc);

        let backup_values = self.mop_graph.values.clone(); // duplicate the status when visiteding different paths;
        let backup_constant = self.mop_graph.constants.clone();
        let backup_alias_sets = self.mop_graph.alias_sets.clone();
        let backup_drop_record = self.drop_record.clone();
        for raw_path in &paths_in_scc {
            let path = &raw_path.0;
            let path_constants = &raw_path.1;

            if !path.is_empty() {
                for idx in &path[..path.len() - 1] {
                    self.alias_bb(*idx);
                    self.alias_bbcall(*idx, fn_map);
                    self.drop_check(*idx);
                }
            }
            // The last node is already ouside the scc.
            if let Some(&last_node) = path.last() {
                if self.mop_graph.blocks[last_node].scc.nodes.is_empty() {
                    self.check_single_node(last_node, fn_map);
                    self.handle_nexts(last_node, fn_map, None, Some(path_constants));
                } else {
                    // TODO
                }
            }
            self.mop_graph.alias_sets = backup_alias_sets.clone();
            self.mop_graph.values = backup_values.clone();
            self.mop_graph.constants = backup_constant.clone();
            self.drop_record = backup_drop_record.clone();
        }
    }

    pub fn check_single_node(&mut self, bb_idx: usize, fn_map: &MopAAResultMap) {
        let cur_block = self.mop_graph.blocks[bb_idx].clone();
        rap_debug!("check {:?} as a node", bb_idx);
        self.alias_bb(bb_idx);
        self.alias_bbcall(bb_idx, fn_map);
        self.drop_check(bb_idx);

        // For dangling pointer check;
        // Since a node within an SCC cannot be an exit, we only check for non-scc nodes;
        if cur_block.next.is_empty() {
            if should_check(self.mop_graph.def_id) {
                self.dp_check(cur_block.is_cleanup);
            }
        }
    }

    pub fn handle_nexts(
        &mut self,
        bb_idx: usize,
        fn_map: &MopAAResultMap,
        exclusive_nodes: Option<&FxHashSet<usize>>,
        path_constraints: Option<&FxHashMap<usize, usize>>,
    ) {
        let cur_block = self.mop_graph.blocks[bb_idx].clone();
        let tcx = self.mop_graph.tcx;

        // Extra path contraints are introduced during scc handling.
        if let Some(path_constants) = path_constraints {
            self.mop_graph.constants.extend(path_constants);
        }

        /* Begin: handle the SwitchInt statement. */
        let mut single_target = false;
        let mut sw_val = 0;
        let mut sw_target = 0; // Single target
        let mut path_discr_id = 0; // To avoid analyzing paths that cannot be reached with one enum type.
        let mut sw_targets = None; // Multiple targets of SwitchInt
        if let Term::Switch(switch) = &cur_block.terminator {
            rap_debug!("Handle switchInt in bb {:?}", cur_block);
            if let TerminatorKind::SwitchInt {
                ref discr,
                ref targets,
            } = switch.kind
            {
                rap_debug!("{:?}", switch);
                rap_debug!("{:?}", self.mop_graph.constants);
                match discr {
                    Copy(p) | Move(p) => {
                        let value_idx = self.projection(*p);
                        let local_decls = &tcx.optimized_mir(self.mop_graph.def_id).local_decls;
                        let place_ty = (*p).ty(local_decls, tcx);
                        rap_debug!("value_idx: {:?}", value_idx);
                        match place_ty.ty.kind() {
                            TyKind::Bool => {
                                rap_debug!("SwitchInt via Bool");
                                if let Some(constant) = self.mop_graph.constants.get(&value_idx) {
                                    if *constant != usize::MAX {
                                        single_target = true;
                                        sw_val = *constant;
                                    }
                                }
                                path_discr_id = value_idx;
                                sw_targets = Some(targets.clone());
                            }
                            _ => {
                                if let Some(father) = self
                                    .mop_graph
                                    .discriminants
                                    .get(&self.mop_graph.values[value_idx].local)
                                {
                                    if let Some(constant) = self.mop_graph.constants.get(father) {
                                        if *constant != usize::MAX {
                                            single_target = true;
                                            sw_val = *constant;
                                        }
                                    }
                                    if self.mop_graph.values[value_idx].local == value_idx {
                                        path_discr_id = *father;
                                        sw_targets = Some(targets.clone());
                                    }
                                }
                            }
                        }
                    }
                    Constant(c) => {
                        single_target = true;
                        let ty_env = TypingEnv::post_analysis(tcx, self.mop_graph.def_id);
                        if let Some(val) = c.const_.try_eval_target_usize(tcx, ty_env) {
                            sw_val = val as usize;
                        }
                    }
                }
                if single_target {
                    /* Find the target based on the value;
                     * Since sw_val is a const, only one target is reachable.
                     * Filed 0 is the value; field 1 is the real target.
                     */
                    for iter in targets.iter() {
                        if iter.0 as usize == sw_val {
                            sw_target = iter.1.as_usize();
                            break;
                        }
                    }
                    /* No target found, choose the default target.
                     * The default targets is not included within the iterator.
                     * We can only obtain the default target based on the last item of all_targets().
                     */
                    if sw_target == 0 {
                        let all_target = targets.all_targets();
                        sw_target = all_target[all_target.len() - 1].as_usize();
                    }
                }
            }
        }
        /* End: finish handling SwitchInt */
        // fixed path since a constant switchInt value
        if single_target {
            match exclusive_nodes {
                Some(exclusive) => {
                    if !exclusive.contains(&sw_target) {
                        self.check(sw_target, fn_map);
                    }
                }
                None => {
                    self.check(sw_target, fn_map);
                }
            }
        } else {
            // Other cases in switchInt terminators
            if let Some(targets) = sw_targets {
                for iter in targets.iter() {
                    if self.mop_graph.visit_times > VISIT_LIMIT {
                        continue;
                    }
                    let next = iter.1.as_usize();

                    match exclusive_nodes {
                        Some(exclusive) => {
                            if exclusive.contains(&next) {
                                continue;
                            }
                        }
                        None => {}
                    }
                    let path_discr_val = iter.0 as usize;
                    self.split_check_with_cond(next, path_discr_id, path_discr_val, fn_map);
                }
                let all_targets = targets.all_targets();
                let next_idx = all_targets[all_targets.len() - 1].as_usize();
                let path_discr_val = usize::MAX; // to indicate the default path;
                self.split_check_with_cond(next_idx, path_discr_id, path_discr_val, fn_map);
            } else {
                for next in &cur_block.next {
                    if self.mop_graph.visit_times > VISIT_LIMIT {
                        continue;
                    }

                    match exclusive_nodes {
                        Some(exclusive) => {
                            if exclusive.contains(&next) {
                                continue;
                            }
                        }
                        None => {}
                    }
                    self.split_check(*next, fn_map);
                }
            }
        }
    }
}
