use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use crate::analysis::senryx::visitor::PlaceTy;

#[derive(Debug, PartialEq, PartialOrd, Copy, Clone)]
pub enum Value {
    Usize(usize),
    Isize(isize),
    U32(u32),
    Custom(),
    None,
    // ...
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum StateType<'tcx> {
    AllocatedState(AllocatedState),
    AlignState(AlignState<'tcx>),
    // ...
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Op {
    EQ,
    NE,
    LT,
    GT,
    LE,
    GE,
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum AllocatedState {
    Top,
    Borrowed,
    Moved,
    Alloc,
    SpecificAlloc,
    Bottom,
}

use crate::analysis::senryx::symbolic_analysis::{AnaOperand, SymbolicDef};
use rustc_middle::ty::Ty;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AlignState<'tcx> {
    Aligned(Ty<'tcx>, u64),
    Unaligned(Ty<'tcx>, u64, SymbolicDef),
    Unknown,
}

impl<'tcx> AlignState<'tcx> {
    pub fn merge(&self, other: &Self) -> Self {
        if self == other {
            return other.clone();
        }
        match (self, other) {
            (AlignState::Aligned(t1, a1), AlignState::Aligned(t2, a2)) => {
                if t1 == t2 {
                    AlignState::Aligned(*t1, std::cmp::min(*a1, *a2))
                } else {
                    AlignState::Unknown
                }
            }
            (AlignState::Unaligned(t1, a1, off1), AlignState::Unaligned(t2, a2, off2)) => {
                AlignState::Unknown
            }
            _ => AlignState::Unknown,
        }
    }
}

// #[derive(Debug, PartialEq, Eq, Clone, Hash)]
// pub enum AlignState<'tcx> {
//     Aligned,
//     Cast(PlaceTy<'tcx>, PlaceTy<'tcx>),
//     Unaligned,
// }

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub enum InitState {
    FullyInitialized,
    PartlyInitialized,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum VType<'tcx> {
    Pointer(PlaceTy<'tcx>),
    None,
    // todo
}
