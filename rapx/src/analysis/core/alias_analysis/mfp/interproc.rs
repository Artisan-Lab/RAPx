/// Interprocedural analysis utilities
extern crate rustc_mir_dataflow;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Body, TerminatorKind};
use rustc_mir_dataflow::ResultsCursor;

use super::super::{AliasPair, FnAliasPairs};
use super::intraproc::{FnAliasAnalyzer, PlaceId};

/// Extract root local and field path from a PlaceId
/// Returns (root_local, field_path)
fn extract_fields(place: &PlaceId) -> (usize, Vec<usize>) {
    let mut fields = Vec::new();
    let mut current = place;

    // Traverse from leaf to root, collecting field indices
    loop {
        match current {
            PlaceId::Local(idx) => return (*idx, fields),
            PlaceId::Field { base, field_idx } => {
                fields.push(*field_idx);
                current = base;
            }
        }
    }
}

/// Extract function summary from analysis results
pub fn extract_summary<'tcx>(
    results: &mut ResultsCursor<'_, 'tcx, FnAliasAnalyzer<'tcx>>,
    body: &Body<'tcx>,
    _def_id: DefId,
) -> FnAliasPairs {
    let arg_count = body.arg_count;
    let mut summary = FnAliasPairs::new(arg_count);

    // Find all Return terminators and extract aliases at those points
    for (block_id, block_data) in body.basic_blocks.iter_enumerated() {
        if let Some(terminator) = &block_data.terminator {
            if matches!(terminator.kind, TerminatorKind::Return) {
                // Seek to the end of this block (before the terminator)
                results.seek_to_block_end(block_id);

                let state = results.get();
                let analyzer = results.analysis();
                let place_info = analyzer.place_info();

                // Extract field-sensitive aliases between arguments and return value
                // Iterate through all places and check if they are aliased
                for idx_i in 0..place_info.num_places() {
                    for idx_j in (idx_i + 1)..place_info.num_places() {
                        // Check if these two places are aliased
                        if state.clone().are_aliased(idx_i, idx_j) {
                            // Get the PlaceId for each index
                            if let (Some(place_i), Some(place_j)) =
                                (place_info.get_place(idx_i), place_info.get_place(idx_j))
                            {
                                // Extract root local and field paths
                                let (root_i, mut fields_i) = extract_fields(place_i);
                                let (root_j, mut fields_j) = extract_fields(place_j);

                                // Only include aliases involving arguments/return value
                                // Index 0 is return value, indices 1..=arg_count are arguments
                                if root_i <= arg_count && root_j <= arg_count {
                                    // Fields were collected from leaf to root, reverse them
                                    fields_i.reverse();
                                    fields_j.reverse();

                                    // Create field-sensitive AliasPair
                                    let mut alias = AliasPair::new(root_i, root_j);
                                    alias.lhs_fields = fields_i;
                                    alias.rhs_fields = fields_j;
                                    summary.add_alias(alias);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    summary
}

/// Join two function summaries
pub fn join_fn_summaries(summary1: &FnAliasPairs, summary2: &FnAliasPairs) -> FnAliasPairs {
    // TODO: Implement summary join operation
    let mut result = FnAliasPairs::new(summary1.arg_size());

    // Add all aliases from both summaries
    for alias in summary1.aliases() {
        result.add_alias(alias.clone());
    }

    for alias in summary2.aliases() {
        result.add_alias(alias.clone());
    }

    result
}
