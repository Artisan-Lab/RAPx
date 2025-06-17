#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]

use rustc_data_structures::graph::dominators::Dominators;
use rustc_data_structures::graph::{dominators, Predecessors};
use rustc_hir::def_id::DefId;
use rustc_hir::def_id::{CrateNum, DefIndex, LocalDefId, CRATE_DEF_INDEX, LOCAL_CRATE};
use rustc_middle::mir::*;
use rustc_middle::{
    mir::{visit::Visitor, Body, Local, Location},
    ty::TyCtxt,
};
use rustc_span::symbol::Symbol;
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
pub struct PhiPlaceholder;
pub struct SSATransformer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
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
    pub phi_def_id: DefId,
    pub essa_def_id: DefId,
    pub locals_map: HashMap<Local, HashSet<Local>>,
    pub ssa_locals_map: HashMap<Local, HashSet<Local>>,
}

impl<'tcx> SSATransformer<'tcx> {
    pub fn print_ssatransformer(&self) {
        // println!("SSATransformer:");
        // println!("cfg: {:?}", self.cfg);
        // println!("dominators: {:?}", self.dominators);
        // println!("dom_tree: {:?}", self.dom_tree);
        // println!("df: {:?}", self.df);
        // println!("local_assign_blocks: {:?}", self.local_assign_blocks);
        // println!("reaching_def: {:?}", self.reaching_def);
        // println!("local_index: {:?}", self.local_index);
        // println!("local_defination_block: {:?}", self.local_defination_block);
        // println!("skipped: {:?}", self.skipped);
        // println!("phi_index: {:?}", self.phi_index);
        // println!("phi_statements: {:?}", self.phi_statements);
        // println!("essa_statements: {:?}", self.essa_statements);
    }
    fn find_phi_placeholder(tcx: TyCtxt<'_>, crate_name: &str) -> Option<DefId> {
        let sym_crate = Symbol::intern(crate_name);
        let krate = tcx
            .crates(())
            .iter()
            .find(|&&c| tcx.crate_name(c) == sym_crate)?;
        let root_def_id = DefId {
            krate: *krate,
            index: CRATE_DEF_INDEX,
        };
        // print!("Phid\n");

        for item in tcx.module_children(root_def_id) {
            // println!("Module child: {:?}", item.ident.name.as_str());

            if item.ident.name.as_str() == "PhiPlaceholder" {
                if let Some(def_id) = item.res.opt_def_id() {
                    return Some(def_id);
                }
            }
        }
        // print!("Phid\n");
        return Some(root_def_id);
    }
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        ssa_def_id: DefId,
        essa_def_id: DefId,
    ) -> Self {
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
        // let phi_def_id = tcx.type_of(tcx.local_def_id_to_hir_id(def_id).owner.to_def_id());
        // print!("phi_def_id: {:?}\n", def_id);
        // let phi_defid = Self::find_phi_placeholder(tcx, "RAP-interval-demo");
        // if let Some(def_id) = phi_defid {
        //     print!("phi_def_id: {:?}\n", def_id);
        // } else {
        //     print!("phi_def_id not found\n");
        // }
        // let phi_ty = tcx.type_of(def_id).skip_binder();
        // print!("phi_ty: {:?}\n", phi_ty);
        // let crate_num: CrateNum = CrateNum::new(10); // LOCAL_CRATE 是当前 crate，或者用 CrateNum::new(0)
        // let def_index: DefIndex = CRATE_DEF_INDEX; // 这通常是 0，也可以用 DefIndex::from_usize(123)
        // let my_def_id = DefId { krate: crate_num, index: def_index };

        SSATransformer {
            tcx,
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
            phi_def_id: ssa_def_id,
            essa_def_id: essa_def_id,
            locals_map: HashMap::default(),
            ssa_locals_map: HashMap::default(),
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
