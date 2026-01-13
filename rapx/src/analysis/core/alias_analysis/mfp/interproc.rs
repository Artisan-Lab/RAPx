/// Interprocedural analysis utilities
extern crate rustc_mir_dataflow;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Body, TerminatorKind};
use rustc_mir_dataflow::ResultsCursor;

use super::super::{AliasPair, FnAliasPairs};
use super::intraproc::{FnAliasAnalyzer, PlaceId};

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

                // Extract aliases between arguments and return value
                // Index 0 is return value, indices 1..=arg_count are arguments
                for i in 0..=arg_count {
                    for j in (i + 1)..=arg_count {
                        let place_i = PlaceId::Local(i);
                        let place_j = PlaceId::Local(j);

                        if let (Some(idx_i), Some(idx_j)) = (
                            place_info.get_index(&place_i),
                            place_info.get_index(&place_j),
                        ) {
                            // Check if they are aliased
                            if state.clone().are_aliased(idx_i, idx_j) {
                                let alias = AliasPair::new(i, j);
                                summary.add_alias(alias);
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
