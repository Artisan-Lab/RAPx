use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        Operand::{self, Constant, Copy, Move},
        SwitchTargets, TerminatorKind,
    },
    ty::{TyKind, TypingEnv},
};

use std::collections::HashSet;

use crate::analysis::graphs::scc::{SccInfo, SccTree};

use super::{block::Term, graph::*, *};

impl<'tcx> MopGraph<'tcx> {
    pub fn split_check(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopAAResultMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        /* duplicate the status before visiting a path; */
        let backup_values = self.values.clone(); // duplicate the status when visiting different paths;
        let backup_constant = self.constants.clone();
        let backup_alias_sets = self.alias_sets.clone();
        self.check(bb_idx, fn_map, recursion_set);
        /* restore after visit */
        self.alias_sets = backup_alias_sets;
        self.values = backup_values;
        self.constants = backup_constant;
    }
    pub fn split_check_with_cond(
        &mut self,
        bb_idx: usize,
        path_discr_id: usize,
        path_discr_val: usize,
        fn_map: &mut MopAAResultMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        /* duplicate the status before visiting a path; */
        let backup_values = self.values.clone(); // duplicate the status when visiting different paths;
        let backup_constant = self.constants.clone();
        let backup_alias_sets = self.alias_sets.clone();
        /* add control-sensitive indicator to the path status */
        self.constants.insert(path_discr_id, path_discr_val);
        self.check(bb_idx, fn_map, recursion_set);
        /* restore after visit */
        self.alias_sets = backup_alias_sets;
        self.values = backup_values;
        self.constants = backup_constant;
    }

    // the core function of the alias analysis algorithm.
    pub fn check(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopAAResultMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        self.visit_times += 1;
        if self.visit_times > VISIT_LIMIT {
            return;
        }
        let scc_idx = self.blocks[bb_idx].scc.enter;
        let cur_block = self.blocks[bb_idx].clone();

        rap_debug!("check {:?}", bb_idx);
        if bb_idx == scc_idx && !cur_block.scc.nodes.is_empty() {
            rap_debug!("check {:?} as a scc", bb_idx);
            self.check_scc(bb_idx, fn_map, recursion_set);
        } else {
            self.check_single_node(bb_idx, fn_map, recursion_set);
            self.handle_nexts(bb_idx, fn_map, None, recursion_set);
        }
    }

    pub fn check_scc(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopAAResultMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        let cur_block = self.blocks[bb_idx].clone();

        /* Handle cases if the current block is a merged scc block with sub block */
        rap_debug!("Searchng paths in scc: {:?}, {:?}", bb_idx, cur_block.scc);
        let scc_tree = self.sort_scc_tree(&cur_block.scc);
        rap_debug!("scc_tree: {:?}", scc_tree);
        let paths_in_scc = self.find_scc_paths(bb_idx, &scc_tree, &mut FxHashMap::default());
        rap_info!("Paths found in scc: {:?}", paths_in_scc);

        let backup_values = self.values.clone(); // duplicate the status when visiteding different paths;
        let backup_constant = self.constants.clone();
        let backup_alias_sets = self.alias_sets.clone();
        let backup_fn_map = fn_map.clone();
        let backup_recursion_set = recursion_set.clone();
        for raw_path in paths_in_scc {
            self.alias_sets = backup_alias_sets.clone();
            self.values = backup_values.clone();
            self.constants = backup_constant.clone();
            *fn_map = backup_fn_map.clone();
            *recursion_set = backup_recursion_set.clone();

            let path = raw_path.0;
            let path_constraints = &raw_path.1;
            rap_info!("checking path: {:?}", path);
            if !path.is_empty() {
                for idx in &path[..path.len() - 1] {
                    self.alias_bb(*idx);
                    self.alias_bbcall(*idx, fn_map, recursion_set);
                }
            }
            // The last node is already ouside the scc.
            if let Some(&last_node) = path.last() {
                if self.blocks[last_node].scc.nodes.is_empty() {
                    self.check_single_node(last_node, fn_map, recursion_set);
                    self.handle_nexts(last_node, fn_map, Some(path_constraints), recursion_set);
                } else {
                    // If the exit is an scc, we should handle it like check_scc;
                }
            }
        }
    }

    pub fn check_single_node(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopAAResultMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        rap_debug!("check {:?} as a node", bb_idx);
        let cur_block = self.blocks[bb_idx].clone();
        self.alias_bb(self.blocks[bb_idx].scc.enter);
        self.alias_bbcall(self.blocks[bb_idx].scc.enter, fn_map, recursion_set);
        if cur_block.next.is_empty() {
            self.merge_results(self.values.clone());
            return;
        }
    }

    pub fn handle_nexts(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopAAResultMap,
        path_constraints: Option<&FxHashMap<usize, usize>>,
        recursion_set: &mut HashSet<DefId>,
    ) {
        let cur_block = self.blocks[bb_idx].clone();
        let tcx = self.tcx;

        rap_debug!(
            "handle nexts {:?} of node {:?}",
            self.blocks[bb_idx].next,
            bb_idx
        );
        // Extra path contraints are introduced during scc handling.
        if let Some(path_constraints) = path_constraints {
            self.constants.extend(path_constraints);
        }
        /* Begin: handle the SwitchInt statement. */
        let mut single_target = false;
        let mut sw_val = 0;
        let mut sw_target = 0; // Single target
        let mut path_discr_id = 0; // To avoid analyzing paths that cannot be reached with one enum type.
        let mut sw_targets = None; // Multiple targets of SwitchInt

        match cur_block.terminator {
            Term::Switch(switch) => {
                if let TerminatorKind::SwitchInt {
                    ref discr,
                    ref targets,
                } = switch.kind
                {
                    match discr {
                        Copy(p) | Move(p) => {
                            let value_idx = self.projection(*p);
                            let local_decls = &tcx.optimized_mir(self.def_id).local_decls;
                            let place_ty = (*p).ty(local_decls, tcx);
                            rap_debug!("value_idx: {:?}", value_idx);
                            match place_ty.ty.kind() {
                                TyKind::Bool => {
                                    if let Some(constant) = self.constants.get(&value_idx) {
                                        if *constant != usize::MAX {
                                            single_target = true;
                                            sw_val = *constant;
                                        }
                                    }
                                    path_discr_id = value_idx;
                                    sw_targets = Some(targets.clone());
                                }
                                _ => {
                                    if let Some(father) =
                                        self.discriminants.get(&self.values[value_idx].local)
                                    {
                                        if let Some(constant) = self.constants.get(father) {
                                            if *constant != usize::MAX {
                                                single_target = true;
                                                sw_val = *constant;
                                            }
                                        }
                                        if self.values[value_idx].local == value_idx {
                                            path_discr_id = *father;
                                            sw_targets = Some(targets.clone());
                                        }
                                    }
                                }
                            }
                        }
                        Constant(c) => {
                            single_target = true;
                            let ty_env = TypingEnv::post_analysis(tcx, self.def_id);
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
                        rap_debug!("targets: {:?}; sw_val = {:?}", targets, sw_val);
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
            _ => {
                // Not SwitchInt
            }
        }
        /* End: finish handling SwitchInt */
        // fixed path since a constant switchInt value
        if single_target {
            rap_debug!("visit a single target: {:?}", sw_target);
            self.check(sw_target, fn_map, recursion_set);
        } else {
            // Other cases in switchInt terminators
            if let Some(targets) = sw_targets {
                for iter in targets.iter() {
                    if self.visit_times > VISIT_LIMIT {
                        continue;
                    }
                    let next = iter.1.as_usize();
                    let path_discr_val = iter.0 as usize;
                    self.split_check_with_cond(
                        next,
                        path_discr_id,
                        path_discr_val,
                        fn_map,
                        recursion_set,
                    );
                }
                let all_targets = targets.all_targets();
                let next_index = all_targets[all_targets.len() - 1].as_usize();
                let path_discr_val = usize::MAX; // to indicate the default path;
                self.split_check_with_cond(
                    next_index,
                    path_discr_id,
                    path_discr_val,
                    fn_map,
                    recursion_set,
                );
            } else {
                for next in cur_block.next {
                    if self.visit_times > VISIT_LIMIT {
                        continue;
                    }
                    self.split_check(next, fn_map, recursion_set);
                }
            }
        }
    }

    pub fn sort_scc_tree(&mut self, scc: &SccInfo) -> SccTree {
        // child_enter -> SccInfo
        let mut child_sccs: FxHashMap<usize, SccInfo> = FxHashMap::default();

        // find all sub sccs
        for &node in scc.nodes.iter() {
            let node_scc = &self.blocks[node].scc;
            if node_scc.enter != scc.enter && !node_scc.nodes.is_empty() {
                child_sccs
                    .entry(node_scc.enter)
                    .or_insert_with(|| node_scc.clone());
            }
        }

        // recursively sort children
        let children = child_sccs
            .into_values()
            .map(|child_scc| self.sort_scc_tree(&child_scc))
            .collect();

        SccTree {
            scc: scc.clone(),
            children,
        }
    }

    pub fn find_scc_paths(
        &mut self,
        start: usize,
        scc_tree: &SccTree,
        path_constraints: &mut FxHashMap<usize, usize>,
    ) -> Vec<(Vec<usize>, FxHashMap<usize, usize>)> {
        let mut all_paths = Vec::new();
        let mut scc_path_set: HashSet<Vec<usize>> = HashSet::new();

        self.find_scc_paths_inner(
            start,
            start,
            scc_tree,
            &mut vec![start],
            path_constraints,
            &mut all_paths,
            &mut scc_path_set,
        );

        all_paths
    }

    fn find_scc_paths_inner(
        &mut self,
        start: usize,
        cur: usize,
        scc_tree: &SccTree,
        path: &mut Vec<usize>,
        path_constraints: &mut FxHashMap<usize, usize>,
        paths_in_scc: &mut Vec<(Vec<usize>, FxHashMap<usize, usize>)>,
        scc_path_set: &mut HashSet<Vec<usize>>,
    ) {
        rap_debug!("cur = {}", cur);
        let scc = &scc_tree.scc;
        if scc.nodes.is_empty() {
            paths_in_scc.push((path.clone(), path_constraints.clone()));
            return;
        }
        // FIX ME: a temp complexity control;
        if path.len() > 100 || paths_in_scc.len() > 200 {
            return;
        }
        if !scc.nodes.contains(&cur) && start != cur {
            rap_debug!("new path: {:?}", path.clone());
            // we add the next node into the scc path to speedup the traveral outside
            // the scc.
            paths_in_scc.push((path.clone(), path_constraints.clone()));
            return;
        }

        if cur == start && path.len() > 1 {
            let last_index = path[..path.len() - 1]
                .iter()
                .rposition(|&node| node == start)
                .map(|i| i)
                .unwrap_or(0);
            let slice = &path[last_index..];
            rap_debug!("path: {:?}", path);
            rap_debug!("slice: {:?}", slice);
            rap_debug!("set: {:?}", scc_path_set);
            if scc_path_set.contains(slice) {
                return;
            } else {
                scc_path_set.insert(slice.to_vec());
            }
        }

        // Clear the constriants if the local is reassigned in the current block;
        // Otherwise, it cannot reach other branches.
        for local in &self.blocks[cur].assigned_locals {
            rap_debug!(
                "Remove path_constraints {:?}, because it has been reassigned.",
                local
            );
            path_constraints.remove(&local);
        }

        // Find the pathes of inner scc recursively;
        for child_tree in &scc_tree.children {
            let child_enter = child_tree.scc.enter;
            if cur == child_enter {
                let sub_paths = self.find_scc_paths(child_enter, child_tree, path_constraints);
                rap_debug!("paths in sub scc: {}, {:?}", child_enter, sub_paths);
                for (subp, subconst) in sub_paths {
                    let mut new_path = path.clone();
                    new_path.extend(&subp[1..]);
                    let mut new_const = path_constraints.clone();
                    new_const.extend(subconst.iter());
                    self.find_scc_paths_inner(
                        start,
                        *new_path.last().unwrap(),
                        scc_tree,
                        &mut new_path,
                        &mut new_const,
                        paths_in_scc,
                        scc_path_set,
                    );
                }
                return;
            }
        }

        let term = &self.terminators[cur].clone();

        rap_debug!("term: {:?}", term);
        match term {
            TerminatorKind::SwitchInt { discr, targets } => {
                self.handle_switch_int_case(
                    start,
                    cur,
                    path,
                    scc_tree,
                    path_constraints,
                    paths_in_scc,
                    discr,
                    targets,
                    scc_path_set,
                );
            }
            _ => {
                for next in self.blocks[cur].next.clone() {
                    path.push(next);
                    self.find_scc_paths_inner(
                        start,
                        next,
                        scc_tree,
                        path,
                        path_constraints,
                        paths_in_scc,
                        scc_path_set,
                    );
                    rap_debug!("pop 1 : {:?}", path.last());
                    path.pop();
                }
            }
        }
    }

    fn handle_switch_int_case(
        &mut self,
        start: usize,
        _cur: usize,
        path: &mut Vec<usize>,
        scc_tree: &SccTree,
        path_constraints: &mut FxHashMap<usize, usize>,
        paths_in_scc: &mut Vec<(Vec<usize>, FxHashMap<usize, usize>)>,
        discr: &Operand<'tcx>,
        targets: &SwitchTargets,
        scc_path_set: &mut std::collections::HashSet<Vec<usize>>,
    ) {
        let place = match discr {
            Copy(p) | Move(p) => Some(self.projection(*p)),
            _ => None,
        };

        if let Some(place) = place {
            let discr_local = self
                .discriminants
                .get(&self.values[place].local)
                .cloned()
                .unwrap_or(place);

            rap_debug!(
                "Handle SwitchInt, discr = {:?}, local = {:?}",
                discr,
                discr_local
            );
            if let Some(&constant) = path_constraints.get(&discr_local) {
                rap_debug!("constant = {:?}", constant);
                rap_debug!("targets = {:?}", targets);
                let mut otherwise = true;
                // Only the branch matching constant
                targets
                    .iter()
                    .filter(|t| t.0 as usize == constant)
                    .for_each(|branch| {
                        let target = branch.1.as_usize();
                        path.push(target);
                        self.find_scc_paths_inner(
                            start,
                            target,
                            scc_tree,
                            path,
                            path_constraints,
                            paths_in_scc,
                            scc_path_set,
                        );
                        rap_debug!("pop 2: {:?}", path.last());
                        path.pop();
                        otherwise = false;
                    });
                if otherwise {
                    let target = targets.otherwise().as_usize();
                    path.push(target);
                    path_constraints.insert(discr_local, targets.iter().len());
                    self.find_scc_paths_inner(
                        start,
                        target,
                        scc_tree,
                        path,
                        path_constraints,
                        paths_in_scc,
                        scc_path_set,
                    );
                    path_constraints.remove(&discr_local);
                    rap_debug!("pop 3: {:?}", path.last());
                    path.pop();
                }
            } else {
                // No restriction, try each branch
                for branch in targets.iter() {
                    let constant = branch.0 as usize;
                    let target = branch.1.as_usize();
                    path.push(target);
                    path_constraints.insert(discr_local, constant);
                    self.find_scc_paths_inner(
                        start,
                        target,
                        scc_tree,
                        path,
                        path_constraints,
                        paths_in_scc,
                        scc_path_set,
                    );
                    path_constraints.remove(&discr_local);
                    rap_debug!("pop 4: {:?}", path.last());
                    path.pop();
                }
                // Handle default branch
                let target = targets.otherwise().as_usize();
                path.push(target);
                path_constraints.insert(discr_local, targets.iter().len());
                self.find_scc_paths_inner(
                    start,
                    target,
                    scc_tree,
                    path,
                    path_constraints,
                    paths_in_scc,
                    scc_path_set,
                );
                path_constraints.remove(&discr_local);
                rap_debug!("pop 5: {:?}", path.last());
                path.pop();
            }
        }
    }
}
