use crate::analysis::core::alias::mop::FnMap;
use crate::analysis::safedrop::SafeDropGraph;
use crate::rap_error;
use rustc_data_structures::fx::FxHashSet;
use rustc_middle::mir::Operand::{Constant, Copy, Move};
use rustc_middle::mir::{Operand, Place, TerminatorKind};
use rustc_middle::ty::{TyCtxt, TyKind, TypingEnv};
use std::collections::{HashMap, HashSet};

pub const VISIT_LIMIT: usize = 1000;

impl<'tcx> SafeDropGraph<'tcx> {
    // analyze the drop statement and update the liveness for nodes.
    pub fn drop_check(&mut self, bb_index: usize, tcx: TyCtxt<'tcx>) {
        let cur_block = self.blocks[bb_index].clone();
        for drop in cur_block.drops {
            match drop.kind {
                TerminatorKind::Drop {
                    ref place,
                    target: _,
                    unwind: _,
                    replace: _,
                    drop: _,
                    async_fut: _,
                } => {
                    if !self.drop_heap_item_check(place, tcx) {
                        continue;
                    }
                    let birth = self.scc_indices[bb_index];
                    let drop_local = self.projection(tcx, false, place.clone());
                    let info = drop.source_info.clone();
                    self.dead_node(drop_local, birth, &info, false);
                }
                TerminatorKind::Call {
                    func: _, ref args, ..
                } => {
                    if args.len() > 0 {
                        let birth = self.scc_indices[bb_index];
                        let place = match args[0].node {
                            Operand::Copy(place) => place,
                            Operand::Move(place) => place,
                            _ => {
                                rap_error!("Constant operand exists: {:?}", args[0]);
                                return;
                            }
                        };
                        let drop_local = self.projection(tcx, false, place.clone());
                        let info = drop.source_info.clone();
                        self.dead_node(drop_local, birth, &info, false);
                    }
                }
                _ => {}
            }
        }
    }

    pub fn drop_heap_item_check(&self, place: &Place<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
        let place_ty = place.ty(&tcx.optimized_mir(self.def_id).local_decls, tcx);
        match place_ty.ty.kind() {
            TyKind::Adt(adtdef, ..) => match self.adt_owner.get(&adtdef.did()) {
                None => true,
                Some(owenr_unit) => {
                    let idx = match place_ty.variant_index {
                        Some(vdx) => vdx.index(),
                        None => 0,
                    };
                    if owenr_unit[idx].0.is_owned() || owenr_unit[idx].1.contains(&true) {
                        true
                    } else {
                        false
                    }
                }
            },
            _ => true,
        }
    }

    pub fn split_check(&mut self, bb_index: usize, tcx: TyCtxt<'tcx>, fn_map: &FnMap) {
        /* duplicate the status before visiting a path; */
        let backup_values = self.values.clone(); // duplicate the status when visiting different paths;
        let backup_constant = self.constant.clone();
        let backup_alias_set = self.alias_set.clone();
        let backup_dead = self.dead_record.clone();
        self.check(bb_index, tcx, fn_map);
        /* restore after visit */
        self.values = backup_values;
        self.constant = backup_constant;
        self.alias_set = backup_alias_set;
        self.dead_record = backup_dead;
    }

    pub fn split_check_with_cond(
        &mut self,
        bb_index: usize,
        path_discr_id: usize,
        path_discr_val: usize,
        tcx: TyCtxt<'tcx>,
        fn_map: &FnMap,
    ) {
        /* duplicate the status before visiting a path; */
        let backup_values = self.values.clone(); // duplicate the status when visiting different paths;
        let backup_constant = self.constant.clone();
        let backup_alias_set = self.alias_set.clone();
        let backup_dead = self.dead_record.clone();
        /* add control-sensitive indicator to the path status */
        self.constant.insert(path_discr_id, path_discr_val);
        self.check(bb_index, tcx, fn_map);
        /* restore after visit */
        self.values = backup_values;
        self.constant = backup_constant;
        self.alias_set = backup_alias_set;
        self.dead_record = backup_dead;
    }

    // the core function of the safedrop.
    pub fn check(&mut self, bb_index: usize, tcx: TyCtxt<'tcx>, fn_map: &FnMap) {
        self.visit_times += 1;
        if self.visit_times > VISIT_LIMIT {
            return;
        }
        let cur_block = self.blocks[self.scc_indices[bb_index]].clone();
        self.alias_bb(self.scc_indices[bb_index], tcx);
        self.alias_bbcall(self.scc_indices[bb_index], tcx, fn_map);
        self.drop_check(self.scc_indices[bb_index], tcx);

        if self.child_scc.get(&self.scc_indices[bb_index]).is_some() {
            let init_index = self.scc_indices[bb_index];
            let (init_block, cur_targets, scc_block_set) =
                self.child_scc.get(&init_index).unwrap().clone();

            for enum_index in cur_targets.all_targets() {
                let backup_values = self.values.clone();
                let backup_constant = self.constant.clone();

                let mut block_node = if bb_index == init_index {
                    init_block.clone()
                } else {
                    self.blocks[bb_index].clone()
                };

                if !block_node.switch_stmts.is_empty() {
                    let TerminatorKind::SwitchInt { targets, .. } =
                        block_node.switch_stmts[0].kind.clone()
                    else {
                        unreachable!();
                    };
                    if cur_targets == targets {
                        block_node.next = FxHashSet::default();
                        block_node.next.insert(enum_index.index());
                    }
                }

                let mut work_list = Vec::new();
                let mut work_set = FxHashSet::<usize>::default();
                work_list.push(bb_index);
                work_set.insert(bb_index);
                while !work_list.is_empty() {
                    let current_node = work_list.pop().unwrap();
                    block_node.scc_sub_blocks.push(current_node);
                    let real_node = if current_node != init_index {
                        self.blocks[current_node].clone()
                    } else {
                        init_block.clone()
                    };

                    if real_node.switch_stmts.is_empty() {
                        for next in &real_node.next {
                            block_node.next.insert(*next);
                        }
                    } else {
                        let TerminatorKind::SwitchInt { ref targets, .. } =
                            real_node.switch_stmts[0].kind
                        else {
                            unreachable!();
                        };

                        if cur_targets == *targets {
                            block_node.next.insert(enum_index.index());
                        } else {
                            for next in &real_node.next {
                                block_node.next.insert(*next);
                            }
                        }
                    }

                    if real_node.switch_stmts.is_empty() {
                        for next in &real_node.next {
                            if scc_block_set.contains(next) && !work_set.contains(next) {
                                work_set.insert(*next);
                                work_list.push(*next);
                            }
                        }
                    } else {
                        let TerminatorKind::SwitchInt { ref targets, .. } =
                            real_node.switch_stmts[0].kind
                        else {
                            unreachable!();
                        };

                        if cur_targets == *targets {
                            let next_index = enum_index.index();
                            if scc_block_set.contains(&next_index)
                                && !work_set.contains(&next_index)
                            {
                                work_set.insert(next_index);
                                work_list.push(next_index);
                            }
                        } else {
                            for next in &real_node.next {
                                if scc_block_set.contains(next) && !work_set.contains(next) {
                                    work_set.insert(*next);
                                    work_list.push(*next);
                                }
                            }
                        }
                    }
                }

                /* remove next nodes which are already in the current SCC */
                let mut to_remove = Vec::new();
                for i in block_node.next.iter() {
                    if self.scc_indices[*i] == init_index {
                        to_remove.push(*i);
                    }
                }
                for i in to_remove {
                    block_node.next.remove(&i);
                }

                for i in block_node.scc_sub_blocks.clone() {
                    self.alias_bb(i, tcx);
                    self.alias_bbcall(i, tcx, fn_map);
                    self.drop_check(i, tcx);
                }
                /* Reach a leaf node, check bugs */
                match block_node.next.len() {
                    0 => {
                        // check the bugs.
                        if Self::should_check(self.def_id) {
                            self.dp_check(&cur_block);
                        }
                        return;
                    }
                    _ => {
                        /*
                         * Equivalent to self.check(cur_block.next[0]..);
                         * We cannot use [0] for FxHashSet.
                         */
                        for next in block_node.next {
                            self.check(next, tcx, fn_map);
                        }
                    }
                }

                self.values = backup_values;
                self.constant = backup_constant;
            }

            return;
        }

        let mut order = vec![];
        order.push(vec![]);

        /* Handle cases if the current block is a merged scc block with sub block */
        if !cur_block.scc_sub_blocks.is_empty() {
            match std::env::var_os("SAFEDROP") {
                Some(val) if val == "0" => {
                    order.push(cur_block.scc_sub_blocks.clone());
                }
                _ => {
                    self.calculate_scc_order(
                        &mut cur_block.scc_sub_blocks.clone(),
                        &mut vec![],
                        &mut order,
                        &mut HashMap::new(),
                        bb_index,
                        bb_index,
                        &mut HashSet::new(),
                    );
                }
            }
        }

        let backup_values = self.values.clone(); // duplicate the status when visiting different paths;
        let backup_constant = self.constant.clone();
        let backup_alias_set = self.alias_set.clone();
        for scc_each in order {
            self.alias_set = backup_alias_set.clone();
            self.values = backup_values.clone();
            self.constant = backup_constant.clone();

            if !scc_each.is_empty() {
                for idx in scc_each {
                    self.alias_bb(idx, tcx);
                    self.alias_bbcall(idx, tcx, fn_map);
                }
            }

            let cur_block = cur_block.clone();
            /* Reach a leaf node, check bugs */
            match cur_block.next.len() {
                0 => {
                    if Self::should_check(self.def_id) {
                        self.dp_check(&cur_block);
                    }
                    return;
                }
                1 => {
                    /*
                     * Equivalent to self.check(cur_block.next[0]..);
                     * We cannot use [0] for FxHashSet.
                     */
                    for next in cur_block.next {
                        self.check(next, tcx, fn_map);
                    }
                    return;
                }
                _ => { // multiple blocks
                }
            }

            /* Begin: handle the SwitchInt statement. */
            let mut single_target = false;
            let mut sw_val = 0;
            let mut sw_target = 0; // Single target
            let mut path_discr_id = 0; // To avoid analyzing paths that cannot be reached with one enum type.
            let mut sw_targets = None; // Multiple targets of SwitchInt
            if !cur_block.switch_stmts.is_empty() && cur_block.scc_sub_blocks.is_empty() {
                if let TerminatorKind::SwitchInt {
                    ref discr,
                    ref targets,
                } = cur_block.switch_stmts[0].clone().kind
                {
                    match discr {
                        Copy(p) | Move(p) => {
                            let place = self.projection(tcx, false, *p);
                            if let Some(father) = self.disc_map.get(&self.values[place].local) {
                                if let Some(constant) = self.constant.get(father) {
                                    if *constant != usize::MAX {
                                        single_target = true;
                                        sw_val = *constant;
                                    }
                                }
                                if self.values[place].local == place {
                                    path_discr_id = *father;
                                    sw_targets = Some(targets.clone());
                                }
                            }
                        }
                        Constant(c) => {
                            single_target = true;
                            let ty_env = TypingEnv::post_analysis(self.tcx, self.def_id);
                            if let Some(val) = c.const_.try_eval_target_usize(self.tcx, ty_env) {
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
                self.check(sw_target, tcx, fn_map);
            } else {
                // Other cases in switchInt terminators
                if let Some(targets) = sw_targets {
                    for iter in targets.iter() {
                        if self.visit_times > VISIT_LIMIT {
                            continue;
                        }
                        let next_index = iter.1.as_usize();
                        let path_discr_val = iter.0 as usize;
                        self.split_check_with_cond(
                            next_index,
                            path_discr_id,
                            path_discr_val,
                            tcx,
                            fn_map,
                        );
                    }
                    let all_targets = targets.all_targets();
                    let next_index = all_targets[all_targets.len() - 1].as_usize();
                    let path_discr_val = usize::MAX; // to indicate the default path;
                    self.split_check_with_cond(
                        next_index,
                        path_discr_id,
                        path_discr_val,
                        tcx,
                        fn_map,
                    );
                } else {
                    for i in cur_block.next {
                        if self.visit_times > VISIT_LIMIT {
                            continue;
                        }
                        let next_index = i;
                        self.split_check(next_index, tcx, fn_map);
                    }
                }
            }
        }
    }

    pub fn calculate_scc_order(
        &mut self,
        scc: &Vec<usize>,
        path: &mut Vec<usize>,
        ans: &mut Vec<Vec<usize>>,
        disc_map: &mut HashMap<usize, usize>,
        idx: usize,
        root: usize,
        visit: &mut HashSet<usize>,
    ) {
        if idx == root && !path.is_empty() {
            ans.push(path.clone());
            return;
        }
        visit.insert(idx);
        let term = &self.terms[idx].clone();

        match term {
            TerminatorKind::SwitchInt {
                ref discr,
                ref targets,
            } => match discr {
                Copy(p) | Move(p) => {
                    let place = self.projection(self.tcx, false, *p);
                    if let Some(father) = self.disc_map.get(&self.values[place].local) {
                        let father = *father;
                        if let Some(constant) = disc_map.get(&father) {
                            let constant = *constant;
                            for t in targets.iter() {
                                if t.0 as usize == constant {
                                    let target = t.1.as_usize();
                                    if path.contains(&target) {
                                        continue;
                                    }
                                    path.push(target);
                                    self.calculate_scc_order(
                                        scc, path, ans, disc_map, target, root, visit,
                                    );
                                    path.pop();
                                }
                            }
                        } else {
                            for t in targets.iter() {
                                let constant = t.0 as usize;
                                let target = t.1.as_usize();
                                if path.contains(&target) {
                                    continue;
                                }
                                path.push(target);
                                disc_map.insert(father, constant);
                                self.calculate_scc_order(
                                    scc, path, ans, disc_map, target, root, visit,
                                );
                                disc_map.remove(&father);
                                path.pop();
                            }
                        }
                    } else {
                        if let Some(constant) = disc_map.get(&place) {
                            let constant = *constant;
                            for t in targets.iter() {
                                if t.0 as usize == constant {
                                    let target = t.1.as_usize();
                                    if path.contains(&target) {
                                        continue;
                                    }
                                    path.push(target);
                                    self.calculate_scc_order(
                                        scc, path, ans, disc_map, target, root, visit,
                                    );
                                    path.pop();
                                }
                            }
                        } else {
                            for t in targets.iter() {
                                let constant = t.0 as usize;
                                let target = t.1.as_usize();
                                if path.contains(&target) {
                                    continue;
                                }
                                path.push(target);
                                disc_map.insert(place, constant);
                                self.calculate_scc_order(
                                    scc, path, ans, disc_map, target, root, visit,
                                );
                                disc_map.remove(&place);
                                path.pop();
                            }

                            let constant = targets.iter().len();
                            let target = targets.otherwise().as_usize();
                            if !path.contains(&target) {
                                path.push(target);
                                disc_map.insert(place, constant);
                                self.calculate_scc_order(
                                    scc, path, ans, disc_map, target, root, visit,
                                );
                                disc_map.remove(&place);
                                path.pop();
                            }
                        }
                    }
                }
                _ => {}
            },
            _ => {
                for bidx in self.blocks[idx].next.clone() {
                    if !scc.contains(&bidx) && bidx != root {
                        continue;
                    }
                    if bidx != root {
                        path.push(bidx);
                        self.calculate_scc_order(scc, path, ans, disc_map, bidx, root, visit);
                        path.pop();
                    } else {
                        self.calculate_scc_order(scc, path, ans, disc_map, bidx, root, visit);
                    }
                }
            }
        }

        visit.remove(&idx);
    }
}
