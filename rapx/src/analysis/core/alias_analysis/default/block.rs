use super::assign::*;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::Terminator;
use std::cell::RefCell;

#[derive(Debug, Clone)]
pub struct BlockNode<'tcx> {
    pub index: usize,
    pub is_cleanup: bool,
    pub next: FxHashSet<usize>,
    pub assignments: Vec<Assignment<'tcx>>,
    pub calls: Vec<Terminator<'tcx>>,
    pub drops: Vec<Terminator<'tcx>>,
    //store the index of the basic blocks as a SCC node.
    pub scc_sub_blocks: Vec<usize>,
    //store const values defined in this block, i.e., which id has what value;
    pub const_value: Vec<(usize, usize)>,
    //store switch stmts in current block for the path filtering in path-sensitive analysis.
    pub switch_stmts: Vec<Terminator<'tcx>>,
    pub modified_value: FxHashSet<usize>,
    // (SwitchInt target, enum index) -> outside nodes.
    pub scc_outer: SccOuter,
}

pub type SccOuter = RefCell<Option<FxHashMap<(usize, usize), Vec<usize>>>>;

impl<'tcx> BlockNode<'tcx> {
    pub fn new(index: usize, is_cleanup: bool) -> BlockNode<'tcx> {
        BlockNode {
            index,
            is_cleanup,
            next: FxHashSet::<usize>::default(),
            assignments: Vec::<Assignment<'tcx>>::new(),
            calls: Vec::<Terminator<'tcx>>::new(),
            drops: Vec::<Terminator<'tcx>>::new(),
            scc_sub_blocks: Vec::<usize>::new(),
            const_value: Vec::<(usize, usize)>::new(),
            switch_stmts: Vec::<Terminator<'tcx>>::new(),
            modified_value: FxHashSet::<usize>::default(),
            scc_outer: RefCell::new(None),
        }
    }

    pub fn add_next(&mut self, index: usize) {
        self.next.insert(index);
    }
}
