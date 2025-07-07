#![allow(non_snake_case)]
#![allow(unused_variables)]
#![allow(dead_code)]
pub mod default;
pub mod domain;
use crate::analysis::{core::range_analysis::domain::domain::{ConstConvert, IntervalArithmetic}, Analysis
};
use once_cell::sync::Lazy;
use intervals::{
    Closed,
};

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, BinOp, Place};
use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Debug},
};
pub trait RangeAnalysis<'tcx, T: IntervalArithmetic + ConstConvert + Debug>: Analysis {

    /// Returns the range information for all local variables (Places) in a given function.
    ///
    /// Parameters:
    /// - def_id: The function's unique identifier (DefId)
    ///
    /// Returns:
    /// - A HashMap mapping each Place (variable) in the function to its inferred Range<T>.
    fn get_fn_range(&self, def_id: DefId) -> Option<HashMap<Place<'tcx>, Range<T>>>;

    /// Returns the complete mapping of range information for all functions in the crate.
    ///
    /// Returns:
    /// - A map from DefId (function) to a HashMap of Places and their corresponding ranges.
    fn get_all_fn_ranges(&self) -> FxHashMap<DefId, HashMap<Place<'tcx>, Range<T>>>;

    /// Returns the range for a specific local variable in a specific function.
    ///
    /// Parameters:
    /// - def_id: The function's identifier
    /// - local: The target Place (local variable) within the function
    ///
    /// Returns:
    /// - The inferred Range<T> if available, otherwise None.
    fn get_fn_local_range(&self, def_id: DefId, local: Place<'tcx>) -> Option<Range<T>>;

    /// Returns:
    /// - A set of basic blocks containing `SwitchInt` (branch) terminators.
    /// - A mapping from paths (as sequences of basic block indices) to their corresponding
    ///   control-flow constraints expressed as (Place, Place, BinOp).
    ///
    /// This supports path-sensitive pruning by allowing reasoning over feasible paths.

    fn use_path_constraints_analysis(
        &self,
    ) -> (
        HashSet<BasicBlock>,
        HashMap<Vec<usize>, Vec<(Place<'tcx>, Place<'tcx>, BinOp)>>,
    );
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum RangeType {
    Unknown,
    Regular,
    Empty,
}
impl fmt::Display for RangeType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            RangeType::Unknown => "Unknown",
            RangeType::Regular => "Regular",
            RangeType::Empty => "Empty",
        };
        write!(f, "{}", s)
    }
}
#[derive(Debug, PartialEq, Clone)]
pub struct Range<T>
where
    T: PartialOrd + Clone,
{
    pub rtype: RangeType,
    pub range: Closed<T>,
}

static STR_MIN: Lazy<String> = Lazy::new(|| "Min".to_string());
static STR_MAX: Lazy<String> = Lazy::new(|| "Max".to_string());
impl<T> fmt::Display for Range<T>
where
    T: IntervalArithmetic,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lower = if self.range.left.0 == T::min_value() {
            &*STR_MIN
        } else if self.range.left.0 == T::max_value() {
            &*STR_MAX
        } else {
            return write!(
                f,
                "{} [{}, {}]",
                self.rtype, self.range.left.0, self.range.right.0
            );
        };

        let upper = if self.range.right.0 == T::min_value() {
            &*STR_MIN
        } else if self.range.right.0 == T::max_value() {
            &*STR_MAX
        } else {
            return write!(
                f,
                "{} [{}, {}]",
                self.rtype, self.range.left.0, self.range.right.0
            );
        };
        write!(f, "{} [{}, {}]", self.rtype, lower, upper)
    }
}




