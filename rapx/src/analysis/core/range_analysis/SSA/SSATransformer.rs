use rustc_data_structures::graph::dominators::Dominators;
// use rustc_mir_transform::ssa::SsaLocals;
// use crate::ssa::SsaLocals;
use rustc_data_structures::graph::{dominators, Predecessors};
use rustc_driver::Compilation;
use rustc_driver::{Callbacks, RunCompiler};
use rustc_hir::def_id::LocalDefId;
use rustc_index::IndexVec;
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::mir::pretty::*;
use rustc_middle::mir::*;
use rustc_middle::{
    mir::{visit::Visitor, Body, Local, Location},
    ty::TyCtxt,
};
use rustc_target::abi::FieldIdx;
use std::borrow::Borrow;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::File;
use std::io::{self, Write};
use std::path::PathBuf;
// use tracing::{debug, error, info, warn};

use rustc_data_structures::fx::FxHashMap;

use rustc_index::bit_set::BitSet;
use rustc_index::IndexSlice;
use rustc_middle::mir::visit::*;
use rustc_middle::mir::visit::*;
use rustc_middle::mir::*;

use super::Replacer::*;
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

    pub fn analyze(&self) {
        println!("{:?}", self.cfg);
        println!("{:?}", self.dominators);
        println!("!!!!!!!!!!!!!!!!!!!!!!!!");
        Self::print_dominance_tree(&self.dom_tree, START_BLOCK, 0);
        print!("{:?}", self.df);
        println!("!!!!!!!!!!!!!!!!!!!!!!!!");
        print!("{:?}", self.local_assign_blocks);

        let dir_path = "ssa_mir";

        let mir_file_path = format!("{}/mir_{:?}.txt", dir_path, self.def_id);
        let phi_mir_file_path = format!("{}/ssa_mir_{:?}.txt", dir_path, self.def_id);
        let mut file = File::create(&mir_file_path).unwrap();
        let mut w1 = io::BufWriter::new(&mut file);
        write_mir_pretty(self.tcx, None, &mut w1).unwrap();
        let mut file2 = File::create(&phi_mir_file_path).unwrap();
        let mut w2 = io::BufWriter::new(&mut file2);
        let options = PrettyPrintMirOptions::from_cli(self.tcx);
        write_mir_fn(
            self.tcx,
            &self.body.borrow(),
            &mut |_, _| Ok(()),
            &mut w2,
            options,
        )
        .unwrap();
    }
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

        for (block, block_data) in body.basic_blocks.iter_enumerated() {
            if (predecessors[block].len() > 1) {
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
        println!("{}{:?}", "  ".repeat(depth), current);

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
    // pub fn rename_variables(
    //     &mut self,
    //     tcx: TyCtxt<'tcx>,
    //     body: &mut Body<'tcx>,
    //     dominator_tree: &HashMap<BasicBlock, Vec<BasicBlock>>,
    // ) {
    //     // 初始化每个变量的 reachingDef
    //     for local in body.local_decls.indices() {
    //         self.reaching_def.insert(local, vec![local]);
    //     }

    //     // 深度优先先序遍历支配树
    //     for bb in Self::depth_first_search_postorder(dominator_tree) {
    //         self.process_basic_block(bb, body);
    //     }
    //     // for succ_bb in body.basic_blocks[bb].terminator().successors() {
    //     //     self.process_phi_functions(succ_bb, body);
    //     // }
    // }

    // /// 处理单个基本块
    // fn process_basic_block(&mut self, bb: BasicBlock, body: &mut Body<'tcx>) {
    //     let statements = &mut body.basic_blocks_mut()[bb].statements;

    //     // 线性处理基本块中的每条指令
    //     for stmt in statements.iter_mut() {
    //         match &mut stmt.kind {
    //             StatementKind::Assign(box (place, rvalue)) => {
    //                 // 仅处理非聚合类型的赋值
    //                 if !matches!(rvalue, Rvalue::Aggregate(..)) {
    //                     match rvalue {
    //                         Rvalue::Use(ref mut operand) => {
    //                             self.replace_with_latest_def(operand);
    //                         }
    //                         Rvalue::BinaryOp(op, box (ref mut operand1, ref mut operand2)) => {
    //                             self.replace_with_latest_def(operand1);
    //                             self.replace_with_latest_def(operand2);
    //                         }
    //                         Rvalue::UnaryOp(op, ref mut operand) => {
    //                             self.replace_with_latest_def(operand);
    //                         }
    //                         Rvalue::Repeat(operand, _) => todo!(),
    //                         Rvalue::Ref(region, borrow_kind, place) => todo!(),
    //                         Rvalue::ThreadLocalRef(def_id) => todo!(),
    //                         Rvalue::Len(place) => todo!(),
    //                         Rvalue::Cast(cast_kind, operand, ty) => todo!(),
    //                         Rvalue::NullaryOp(null_op, ty) => todo!(),
    //                         Rvalue::Discriminant(place) => todo!(),
    //                         Rvalue::Aggregate(aggregate_kind, index_vec) => todo!(),
    //                         Rvalue::ShallowInitBox(operand, ty) => todo!(),
    //                         Rvalue::CopyForDeref(place) => todo!(),
    //                         Rvalue::RawPtr(mutability, place) => todo!(),
    //                     }
    //                     // 遍历 rvalue 中的操作数，并执行变量重命名
    //                     // for operand in rvalue.operands_mut() {
    //                     //     if let Operand::Copy(place) | Operand::Move(place) = operand {
    //                     //         if let Some(local) = place.as_local() {
    //                     //             // 替换使用变量为其最新定义
    //                     //             self.update_reaching_def(local);
    //                     //             if let Some(current_def) =
    //                     //                 self.reaching_def.get(&local).and_then(|stack| stack.last())
    //                     //             {
    //                     //                 *place = Place::from(*current_def);
    //                     //             }
    //                     //         }
    //                     //     }
    //                     // }
    //                 }
    //                 if place.as_local().is_some() {
    //                     // replace_with_latest_def(place);
    //                     // self.rename_def(place, body);
    //                 }
    //             }
    //             _ => {}
    //         }
    //     }

    //     // 处理后继块中的 φ 函数
    //     let successors: Vec<_> = body.basic_blocks_mut()[bb]
    //         .terminator()
    //         .successors()
    //         .collect();
    //     for successor in successors {
    //         self.process_phi_functions(successor, body);
    //     }
    // }

    // /// 重命名指令中的使用变量
    // // fn rename_uses(&mut self, rvalue: &mut Rvalue<'tcx>) {
    // //     // 遍历 Rvalue 中的变量使用
    // //     for operand in rvalue.operands_mut() {
    // //         if let Operand::Copy(place) | Operand::Move(place) = operand {
    // //             if let Some(local) = place.as_local() {
    // //                 if let Some(def_stack) = self.reaching_def.get(&local) {
    // //                     if let Some(current_def) = def_stack.last() {
    // //                         *place = Place::from(*current_def);
    // //                     }
    // //                 }
    // //             }
    // //         }
    // //     }
    // // }

    // // /// 为指令中定义的变量分配新版本
    // fn rename_def(&mut self, place: &mut Place<'tcx>, body: &mut Body<'tcx>) {
    //     if let Some(local) = place.as_local() {
    //         let new_local = self.create_fresh_variable(local, body);
    //         if let Some(def_stack) = self.reaching_def.get_mut(&local) {
    //             def_stack.push(new_local);
    //         }
    //         *place = Place::from(new_local);
    //     }
    // }

    // /// 处理后继块中的 φ 函数
    // fn process_phi_functions(&mut self, bb: BasicBlock, body: &mut Body<'tcx>) {
    //     // if let Some(Terminator {
    //     //     kind: TerminatorKind::Call { args, .. },
    //     //     ..
    //     // }) = &body.basic_blocks[bb].terminator
    //     // {
    //     //     for arg in args {
    //     //         if let Operand::Copy(place) | Operand::Move(place) = arg {
    //     //             if let Some(local) = place.as_local() {
    //     //                 if let Some(def_stack) = self.reaching_def.get(&local) {
    //     //                     if let Some(current_def) = def_stack.last() {
    //     //                         *place = Place::from(*current_def);
    //     //                     }
    //     //                 }
    //     //             }
    //     //         }
    //     //     }
    //     // }
    // }

    // /// 创建一个新的变量版本
    // fn create_fresh_variable(&mut self, local: Local, body: &mut Body<'_>) -> Local {
    //     // 假设新的 Local 分配基于现有的数量
    //     let new_local_index = body.local_decls.len();

    //     // 创建一个新的变量声明
    //     let new_decl = body.local_decls[local].clone();
    //     let new_local = body.local_decls.push(new_decl);
    //     new_local
    // }
    // pub fn insert_phi_statment(&mut self,body: &mut Body<'tcx>) {
    //     // 初始化所有基本块的 phi 函数集合
    //     let mut phi_functions: HashMap<BasicBlock, HashSet<Local>> = HashMap::new();
    //     for bb in self.body.basic_blocks.indices() {
    //         phi_functions.insert(bb, HashSet::new());
    //     }
    //     let variables: Vec<Local> = self
    //         .local_assign_blocks
    //         .iter()
    //         .filter(|(_, blocks)| blocks.len() >= 2) // 只保留基本块数量大于等于 2 的条目
    //         .map(|(&local, _)| local) // 提取 Local
    //         .collect();
    //     print!("{:?}", variables);
    //     for var in &variables {
    //         // 获取变量的定义位置
    //         if let Some(def_blocks) = self.local_assign_blocks.get(var) {
    //             let mut worklist: VecDeque<BasicBlock> = def_blocks.iter().cloned().collect();
    //             let mut processed: HashSet<BasicBlock> = HashSet::new();

    //             while let Some(block) = worklist.pop_front() {
    //                 if let Some(df_blocks) = self.df.get(&block) {
    //                     for &df_block in df_blocks {
    //                         if !processed.contains(&df_block) {
    //                             phi_functions.get_mut(&df_block).unwrap().insert(*var);
    //                             processed.insert(df_block);
    //                             if self.local_assign_blocks[var].contains(&df_block) {
    //                                 worklist.push_back(df_block);
    //                             }
    //                         }
    //                     }
    //                 }
    //             }
    //         }
    //     }

    //     for (block, vars) in phi_functions {
    //         for var in vars {
    //             let decl = self.body.local_decls[var].clone();
    //             let new_var = self.body.local_decls.push(decl);
    //             let predecessors = self.body.basic_blocks.predecessors()[block].clone();

    //             // 构造元组元素，使用占位变量
    //             let mut operands = IndexVec::with_capacity(predecessors.len());
    //             for _ in 0..predecessors.len() {
    //                 operands.push(Operand::Copy(Place::from(var)));
    //             } // 创建 phi 语句
    //             let phi_stmt = Statement {
    //                 source_info: SourceInfo::outermost(self.body.span),
    //                 kind: StatementKind::Assign(Box::new((
    //                     Place::from(new_var), // 左值是变量
    //                     Rvalue::Aggregate(
    //                         Box::new(AggregateKind::Tuple), // 元组类型
    //                         operands,
    //                     ),
    //                 ))),
    //             };

    //             // 插入到基本块的开头
    //             self.body.basic_blocks_mut()[block]
    //                 .statements
    //                 .insert(0, phi_stmt);
    //         }
    //     }
    // }
    // // pub fn insert_phi_statment(&mut self) {
    // //     // 初始化所有基本块的 phi 函数集合
    // //     let mut phi_functions: HashMap<BasicBlock, HashSet<Local>> = HashMap::new();
    // //     for bb in self.body.basic_blocks.indices() {
    // //         phi_functions.insert(bb, HashSet::new());
    // //     }
    // //     let variables: Vec<Local> = self
    // //         .local_assign_blocks
    // //         .iter()
    // //         .filter(|(_, blocks)| blocks.len() >= 2) // 只保留基本块数量大于等于 2 的条目
    // //         .map(|(&local, _)| local) // 提取 Local
    // //         .collect();
    // //     print!("{:?}", variables);
    // //     for var in &variables {
    // //         // 获取变量的定义位置
    // //         if let Some(def_blocks) = self.local_assign_blocks.get(var) {
    // //             let mut worklist: VecDeque<BasicBlock> = def_blocks.iter().cloned().collect();
    // //             let mut processed: HashSet<BasicBlock> = HashSet::new();

    // //             while let Some(block) = worklist.pop_front() {
    // //                 if let Some(df_blocks) = self.df.get(&block) {
    // //                     for &df_block in df_blocks {
    // //                         if !processed.contains(&df_block) {
    // //                             phi_functions.get_mut(&df_block).unwrap().insert(*var);
    // //                             processed.insert(df_block);
    // //                             if self.local_assign_blocks[var].contains(&df_block) {
    // //                                 worklist.push_back(df_block);
    // //                             }
    // //                         }
    // //                     }
    // //                 }
    // //             }
    // //         }
    // //     }

    // //     for (block, vars) in phi_functions {
    // //         for var in vars {
    // //             let decl = self.body.local_decls[var].clone();
    // //             let new_var = self.body.local_decls.push(decl);
    // //             let predecessors = self.body.basic_blocks.predecessors()[block].clone();

    // //             // 构造元组元素，使用占位变量
    // //             let mut operands = IndexVec::with_capacity(predecessors.len());
    // //             for _ in 0..predecessors.len() {
    // //                 operands.push(Operand::Copy(Place::from(var)));
    // //             } // 创建 phi 语句
    // //             let phi_stmt = Statement {
    // //                 source_info: SourceInfo::outermost(self.body.span),
    // //                 kind: StatementKind::Assign(Box::new((
    // //                     Place::from(new_var), // 左值是变量
    // //                     Rvalue::Aggregate(
    // //                         Box::new(AggregateKind::Tuple), // 元组类型
    // //                         operands,
    // //                     ),
    // //                 ))),
    // //             };

    // //             // 插入到基本块的开头
    // //             self.body.basic_blocks_mut()[block]
    // //                 .statements
    // //                 .insert(0, phi_stmt);
    // //         }
    // //     }
    // // }
}
