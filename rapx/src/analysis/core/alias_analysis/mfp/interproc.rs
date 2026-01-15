/// Interprocedural analysis utilities
extern crate rustc_mir_dataflow;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Body, TerminatorKind};
use rustc_mir_dataflow::ResultsCursor;
use std::collections::HashSet;

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
///
/// This function uses transitive closure to identify all aliases related to
/// function parameters and return values, including those connected through
/// temporary variables.
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

                // Step 1: Collect all alias pairs at this return point
                // We need to examine all aliases, not just those directly involving args/return
                let mut all_pairs = Vec::new();
                for idx_i in 0..place_info.num_places() {
                    for idx_j in (idx_i + 1)..place_info.num_places() {
                        if state.clone().are_aliased(idx_i, idx_j) {
                            if let (Some(place_i), Some(place_j)) =
                                (place_info.get_place(idx_i), place_info.get_place(idx_j))
                            {
                                all_pairs.push((idx_i, idx_j, place_i, place_j));
                            }
                        }
                    }
                }

                // Step 2: Initialize relevant_places with all places whose root is a parameter or return value
                // Index 0 is return value, indices 1..=arg_count are arguments
                let mut relevant_places = HashSet::new();
                for idx in 0..place_info.num_places() {
                    if let Some(place) = place_info.get_place(idx) {
                        if place.root_local() <= arg_count {
                            relevant_places.insert(idx);
                        }
                    }
                }

                // Step 3: Expand relevant_places using transitive closure
                // If a place aliases to a relevant place, it becomes relevant too
                // This captures aliases that flow through temporary variables
                // Example: _0 aliases _2, and _2 aliases _1.0, then _2 is relevant
                const MAX_ITERATIONS: usize = 10;
                for iteration in 0..MAX_ITERATIONS {
                    let mut changed = false;
                    for &(idx_i, idx_j, _, _) in &all_pairs {
                        // If one place is relevant and the other isn't, make the other relevant
                        if relevant_places.contains(&idx_i) && !relevant_places.contains(&idx_j) {
                            relevant_places.insert(idx_j);
                            changed = true;
                        }
                        if relevant_places.contains(&idx_j) && !relevant_places.contains(&idx_i) {
                            relevant_places.insert(idx_i);
                            changed = true;
                        }
                    }
                    // Converged when no more places become relevant
                    if !changed {
                        rap_trace!(
                            "Transitive closure converged after {} iterations",
                            iteration + 1
                        );
                        break;
                    }
                }

                // Step 4: Filter and add aliases to summary
                // Only keep aliases where:
                // (a) both places are in relevant_places (connected to args/return through aliases)
                // (b) both roots are args/return (for compact summary representation)
                for (idx_i, idx_j, place_i, place_j) in all_pairs {
                    if relevant_places.contains(&idx_i) && relevant_places.contains(&idx_j) {
                        let (root_i, mut fields_i) = extract_fields(place_i);
                        let (root_j, mut fields_j) = extract_fields(place_j);

                        // Final filter: only include if both roots are parameters or return value
                        // This keeps the summary compact while benefiting from transitive closure
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
