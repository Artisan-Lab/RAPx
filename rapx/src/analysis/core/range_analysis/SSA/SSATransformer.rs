#![allow(unused_imports)]
#![allow(non_snake_case)]
#![allow(unused_variables)]
#![allow(dead_code)]
use rustc_data_structures::graph::dominators::Dominators;
use rustc_data_structures::graph::{dominators, Predecessors};
use rustc_driver::{Callbacks, RunCompiler};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::*;
use rustc_middle::{
    mir::{visit::Visitor, Body, Local, Location},
    ty::TyCtxt,
};
use std::collections::{HashMap, HashSet};

// use std::path::PathBuf;
// // use tracing::{debug, error, info, warn};
// use rustc_target::abi::FieldIdx;
// use std::borrow::Borrow;
// use rustc_index::bit_set::BitSet;
// use rustc_index::IndexSlice;
// use rustc_middle::mir::visit::*;
// use rustc_middle::mir::visit::*;
// use rustc_middle::mir::*;
// use rustc_index::IndexVec;
// use super::Replacer::*;
pub struct SSATransformer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub def_id: LocalDefId,
    pub body: Body<'tcx>,
    pub cfg: HashMap<BasicBlock, Vec<BasicBlock>>,
    pub dominators: Dominators<BasicBlock>,
    pub dom_tree: HashMap<BasicBlock, Vec<BasicBlock>>,
    pub df: HashMap<BasicBlock, HashSet<BasicBlock>>,
    pub local_assign_blocks: HashMap<Local, HashSet<BasicBlock>>,
    pub reaching_def: HashMap<Local, Option<Local>>,
    pub local_index: u32,
    pub local_defination_block: HashMap<Local, BasicBlock>,
    pub skipped: HashSet<u32>,
    pub phi_index: HashMap<*const Statement<'tcx>, usize>,
    pub phi_statements: HashMap<*const Statement<'tcx>, bool>,
    pub essa_statements: HashMap<*const Statement<'tcx>, bool>,
}

impl<'tcx> SSATransformer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, def_id: LocalDefId) -> Self {
        let cfg: HashMap<BasicBlock, Vec<BasicBlock>> = Self::extract_cfg_from_predecessors(&body);

        let dominators: Dominators<BasicBlock> = body.basic_blocks.dominators().clone();

        let dom_tree: HashMap<BasicBlock, Vec<BasicBlock>> = Self::construct_dominance_tree(&body);

        let df: HashMap<BasicBlock, HashSet<BasicBlock>> =
            Self::compute_dominance_frontier(&body, &dom_tree);

        let local_assign_blocks: HashMap<Local, HashSet<BasicBlock>> =
            Self::map_locals_to_assign_blocks(&body);
        let local_defination_block: HashMap<Local, BasicBlock> =
            Self::map_locals_to_definition_block(&body);
        let len = body.local_decls.len() as u32;
        let mut skipped = HashSet::new();
        if len > 0 {
            skipped.extend(1..len + 1);
        }
        SSATransformer {
            tcx,
            def_id,
            body: body.clone(),
            cfg,
            dominators,
            dom_tree,
            df,
            local_assign_blocks,
            reaching_def: HashMap::default(),
            local_index: len as u32,
            local_defination_block: local_defination_block,
            skipped: skipped,
            phi_index: HashMap::default(),
            phi_statements: HashMap::default(),
            essa_statements: HashMap::default(),
        }
    }

    pub fn return_body_ref(&self) -> &Body<'tcx> {
        &self.body
    }

    // pub fn analyze(&self) {
    //     println!("{:?}", self.cfg);
    //     println!("{:?}", self.dominators);
    //     println!("!!!!!!!!!!!!!!!!!!!!!!!!");
    //     Self::print_dominance_tree(&self.dom_tree, START_BLOCK, 0);
    //     print!("{:?}", self.df);
    //     println!("!!!!!!!!!!!!!!!!!!!!!!!!");
    //     print!("{:?}", self.local_assign_blocks);

    //     let dir_path = "ssa_mir";

    //     let mir_file_path = format!("{}/mir_{:?}.txt", dir_path, self.def_id);
    //     let phi_mir_file_path = format!("{}/ssa_mir_{:?}.txt", dir_path, self.def_id);
    //     let mut file = File::create(&mir_file_path).unwrap();
    //     let mut w1 = io::BufWriter::new(&mut file);
    //     write_mir_pretty(self.tcx, None, &mut w1).unwrap();
    //     let mut file2 = File::create(&phi_mir_file_path).unwrap();
    //     let mut w2 = io::BufWriter::new(&mut file2);
    //     let options = PrettyPrintMirOptions::from_cli(self.tcx);
    //     write_mir_fn(
    //         self.tcx,
    //         &self.body.borrow(),
    //         &mut |_, _| Ok(()),
    //         &mut w2,
    //         options,
    //     )
    //     .unwrap();
    // }
    fn map_locals_to_definition_block(body: &Body) -> HashMap<Local, BasicBlock> {
        let mut local_to_block_map: HashMap<Local, BasicBlock> = HashMap::new();

        for (bb, block_data) in body.basic_blocks.iter_enumerated() {
            for statement in &block_data.statements {
                match &statement.kind {
                    StatementKind::Assign(box (place, _)) => {
                        if let Some(local) = place.as_local() {
                            local_to_block_map.entry(local).or_insert(bb);
                        }
                    }
                    _ => {}
                }
            }
        }

        local_to_block_map
    }
    pub fn depth_first_search_preorder(
        dom_tree: &HashMap<BasicBlock, Vec<BasicBlock>>,
        root: BasicBlock,
    ) -> Vec<BasicBlock> {
        let mut visited: HashSet<BasicBlock> = HashSet::new();
        let mut preorder = Vec::new();

        fn dfs(
            node: BasicBlock,
            dom_tree: &HashMap<BasicBlock, Vec<BasicBlock>>,
            visited: &mut HashSet<BasicBlock>,
            preorder: &mut Vec<BasicBlock>,
        ) {
            if visited.insert(node) {
                preorder.push(node);

                if let Some(children) = dom_tree.get(&node) {
                    for &child in children {
                        dfs(child, dom_tree, visited, preorder);
                    }
                }
            }
        }

        dfs(root, dom_tree, &mut visited, &mut preorder);
        preorder
    }
    pub fn depth_first_search_postorder(
        dom_tree: &HashMap<BasicBlock, Vec<BasicBlock>>,
        root: &BasicBlock,
    ) -> Vec<BasicBlock> {
        let mut visited: HashSet<BasicBlock> = HashSet::new();
        let mut postorder = Vec::new();

        fn dfs(
            node: BasicBlock,
            dom_tree: &HashMap<BasicBlock, Vec<BasicBlock>>,
            visited: &mut HashSet<BasicBlock>,
            postorder: &mut Vec<BasicBlock>,
        ) {
            if visited.insert(node) {
                if let Some(children) = dom_tree.get(&node) {
                    for &child in children {
                        dfs(child, dom_tree, visited, postorder);
                    }
                }
                postorder.push(node);
            }
        }

        dfs(*root, dom_tree, &mut visited, &mut postorder);
        postorder
    }

    fn map_locals_to_assign_blocks(body: &Body) -> HashMap<Local, HashSet<BasicBlock>> {
        let mut local_to_blocks: HashMap<Local, HashSet<BasicBlock>> = HashMap::new();

        for (bb, data) in body.basic_blocks.iter_enumerated() {
            for stmt in &data.statements {
                if let StatementKind::Assign(box (place, _)) = &stmt.kind {
                    let local = place.local;

                    local_to_blocks
                        .entry(local)
                        .or_insert_with(HashSet::new)
                        .insert(bb);
                }
            }
        }

        local_to_blocks
    }
    fn construct_dominance_tree(body: &Body<'_>) -> HashMap<BasicBlock, Vec<BasicBlock>> {
        let mut dom_tree: HashMap<BasicBlock, Vec<BasicBlock>> = HashMap::new();
        let dominators = body.basic_blocks.dominators();
        for (block, _) in body.basic_blocks.iter_enumerated() {
            if let Some(idom) = dominators.immediate_dominator(block) {
                dom_tree.entry(idom).or_default().push(block);
            }
        }

        dom_tree
    }
    fn compute_dominance_frontier(
        body: &Body<'_>,
        dom_tree: &HashMap<BasicBlock, Vec<BasicBlock>>,
    ) -> HashMap<BasicBlock, HashSet<BasicBlock>> {
        let mut dominance_frontier: HashMap<BasicBlock, HashSet<BasicBlock>> = HashMap::new();
        let dominators = body.basic_blocks.dominators();
        let predecessors = body.basic_blocks.predecessors();
        for (block, _) in body.basic_blocks.iter_enumerated() {
            dominance_frontier.entry(block).or_default();
        }

        for (block, _) in body.basic_blocks.iter_enumerated() {
            if predecessors[block].len() > 1 {
                let preds = body.basic_blocks.predecessors()[block].clone();

                for &pred in &preds {
                    let mut runner = pred;
                    while runner != dominators.immediate_dominator(block).unwrap() {
                        dominance_frontier.entry(runner).or_default().insert(block);
                        runner = dominators.immediate_dominator(runner).unwrap();
                    }
                }
            }
        }

        dominance_frontier
    }
    fn extract_cfg_from_predecessors(body: &Body<'_>) -> HashMap<BasicBlock, Vec<BasicBlock>> {
        let mut cfg: HashMap<BasicBlock, Vec<BasicBlock>> = HashMap::new();

        for (block, _) in body.basic_blocks.iter_enumerated() {
            for &predecessor in body.basic_blocks.predecessors()[block].iter() {
                cfg.entry(predecessor).or_default().push(block);
            }
        }

        cfg
    }
    fn print_dominance_tree(
        dom_tree: &HashMap<BasicBlock, Vec<BasicBlock>>,
        current: BasicBlock,
        depth: usize,
    ) {
        if let Some(children) = dom_tree.get(&current) {
            for &child in children {
                Self::print_dominance_tree(dom_tree, child, depth + 1);
            }
        }
    }

    pub fn is_phi_statement(&self, statement: &Statement<'tcx>) -> bool {
        let phi_stmt = statement as *const Statement<'tcx>;
        if self.phi_statements.contains_key(&phi_stmt) {
            return true;
        } else {
            return false;
        }
    }
    pub fn is_essa_statement(&self, statement: &Statement<'tcx>) -> bool {
        let essa_stmt = statement as *const Statement<'tcx>;
        if self.essa_statements.contains_key(&essa_stmt) {
            return true;
        } else {
            return false;
        }
    }
}
