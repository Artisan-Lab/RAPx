#![allow(non_snake_case)]
#![allow(unused_variables)]
#![allow(dead_code)]
pub mod default;
pub mod domain;
use crate::analysis::core::range_analysis::domain::{
    domain::{ConstConvert, IntervalArithmetic},
    range::Range,
};

use crate::analysis::Analysis;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, BinOp, Place};
use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
};

pub trait RangeAnalysis<'tcx, T: IntervalArithmetic + ConstConvert + Debug>: Analysis {
    fn get_fn_range(&self, def_id: DefId) -> Option<HashMap<Place<'tcx>, Range<T>>>;
    fn get_all_fn_ranges(&self) -> FxHashMap<DefId, HashMap<Place<'tcx>, Range<T>>>;
    fn get_fn_local_range(&self, def_id: DefId, local: Place<'tcx>) -> Option<Range<T>>;
    // This function is used to get the path constraints analysis results.
    // It returns a set of basicblocks contains SwitchInt and a map from paths to the constraints on this path.
    fn use_path_constraints_analysis(
        &self,
    ) -> (
        HashSet<BasicBlock>,
        HashMap<Vec<usize>, Vec<(Place<'tcx>, Place<'tcx>, BinOp)>>,
    );
}
