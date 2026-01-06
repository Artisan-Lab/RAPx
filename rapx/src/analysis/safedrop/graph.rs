use super::bug_records::*;
use crate::analysis::core::{
    alias_analysis::default::graph::MopGraph, ownedheap_analysis::OHAResultMap,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use std::{fmt, usize, vec::Vec};

#[derive(Debug, Copy, Clone)]
pub struct LocalSpot {
    pub bb: Option<usize>,
    pub local: Option<usize>,
}

impl LocalSpot {
    pub fn new(bb: usize, local: usize) -> Self {
        LocalSpot {
            bb: Some(bb),
            local: Some(local),
        }
    }
    pub fn from_local(local: usize) -> Self {
        LocalSpot {
            bb: None,
            local: Some(local),
        }
    }
    pub fn default() -> Self {
        LocalSpot {
            bb: None,
            local: None,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct DropRecord {
    pub value_index: usize,
    pub is_dropped: bool,
    pub drop_info: LocalSpot,
    pub has_dropped_field: bool,
}

impl DropRecord {
    pub fn new(value_index: usize, is_dropped: bool, drop_info: LocalSpot) -> Self {
        DropRecord {
            value_index,
            is_dropped,
            drop_info,
            has_dropped_field: false,
        }
    }
    pub fn false_record(value_index: usize) -> Self {
        DropRecord {
            value_index,
            is_dropped: false,
            drop_info: LocalSpot::default(),
            has_dropped_field: false,
        }
    }
    pub fn from(value_index: usize, record: &DropRecord) -> Self {
        DropRecord {
            value_index,
            is_dropped: record.is_dropped,
            drop_info: record.drop_info.clone(),
            has_dropped_field: record.has_dropped_field,
        }
    }
}

/// We represent each target function with the `SafeDropGraph` struct and then perform analysis
/// based on the struct.
pub struct SafeDropGraph<'tcx> {
    pub mop_graph: MopGraph<'tcx>,
    pub bug_records: BugRecords,
    pub drop_record: Vec<DropRecord>,
    // analysis of heap item
    pub adt_owner: OHAResultMap,
}

impl<'tcx> SafeDropGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, adt_owner: OHAResultMap) -> Self {
        let mop_graph = MopGraph::new(tcx, def_id);
        let mut drop_record = Vec::<DropRecord>::new();
        for v in &mop_graph.values {
            drop_record.push(DropRecord::false_record(v.index));
        }

        SafeDropGraph {
            mop_graph,
            bug_records: BugRecords::new(),
            drop_record,
            adt_owner,
        }
    }
}

impl<'tcx> std::fmt::Display for SafeDropGraph<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SafeDropGraph {{")?;
        writeln!(f, "  MopGraph: {}", self.mop_graph)?;
        write!(f, "}}")
    }
}
