use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use crate::analysis::senryx::symbolic_analysis::{AnaOperand, SymbolicDef};
use crate::analysis::senryx::visitor::PlaceTy;
use rustc_middle::ty::Ty;

/// Tracks pointer alignment status in the abstract domain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AlignState<'tcx> {
    Aligned(Ty<'tcx>),
    /// Misaligned relative to `u64` by offset `SymbolicDef`.
    Unaligned(Ty<'tcx>, u64, SymbolicDef<'tcx>),
    /// Alignment cannot be statically determined (Top).
    Unknown,
}

impl<'tcx> AlignState<'tcx> {
    /// Merges two states (Lattice Join). Returns the conservative lower bound.
    pub fn merge(&self, other: &Self) -> Self {
        if self == other {
            return other.clone();
        }
        match (self, other) {
            // If both are aligned for the same type, keep the weaker alignment.
            (AlignState::Aligned(t1), AlignState::Aligned(t2)) => {
                if t1 == t2 {
                    AlignState::Aligned(*t1)
                } else {
                    AlignState::Unknown
                }
            }
            // Merging unaligned states is complex; default to Unknown for checking soundness.
            (AlignState::Unaligned(t1, a1, off1), AlignState::Unaligned(t2, a2, off2)) => {
                AlignState::Unknown
            }
            _ => AlignState::Unknown,
        }
    }
}
