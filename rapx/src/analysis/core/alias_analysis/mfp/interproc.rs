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

/// Extract only the field path from a PlaceId (excluding the root local)
/// Returns field indices in order from root to leaf
/// Example: _15.0.1 returns [0, 1]
fn extract_field_path(place: &PlaceId) -> Vec<usize> {
    let mut fields = Vec::new();
    let mut current = place;

    // Traverse from leaf to root
    loop {
        match current {
            PlaceId::Local(_) => {
                fields.reverse(); // Reverse to get root-to-leaf order
                return fields;
            }
            PlaceId::Field { base, field_idx } => {
                fields.push(*field_idx);
                current = base;
            }
        }
    }
}

/// Check if one field path is a proper prefix of another
/// Returns true if `prefix` is a prefix of `full`
///
/// Examples:
///   - is_field_prefix([], [0]) = true  (parent-child)
///   - is_field_prefix([0], [0, 1]) = true  (parent-child)
///   - is_field_prefix([0], [1]) = false  (siblings, not prefix)
///   - is_field_prefix([0, 1], [0, 2]) = false  (different fields at same level)
fn is_field_prefix(prefix: &[usize], full: &[usize]) -> bool {
    if prefix.len() > full.len() {
        return false;
    }
    prefix == &full[..prefix.len()]
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
                for (idx_i, idx_j) in state.get_all_alias_pairs() {
                    if let (Some(place_i), Some(place_j)) =
                        (place_info.get_place(idx_i), place_info.get_place(idx_j))
                    {
                        all_pairs.push((idx_i, idx_j, place_i, place_j));
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
                for _iteration in 0..MAX_ITERATIONS {
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
                        break;
                    }
                }

                // Step 4: Collect candidate aliases from two sources
                //
                // We collect all potential aliases between parameters and return values into
                // a candidate set, which will be filtered and compressed in Step 5.
                //
                // Two sources of candidates:
                //   4.1: Aliases derived through bridge variables (indirect connections)
                //   4.2: Aliases directly present in all_pairs (direct connections)
                //
                let mut candidate_aliases = std::collections::HashSet::new();

                // Step 4.1: Derive aliases through bridge variables
                //
                // Problem: When analyzing complex nested structures (e.g., Vec::from_raw_parts_in),
                // we may have aliases like:
                //   - _0.0.0.0 ≈ _15 (deeply nested field aliases with temporary variable)
                //   - _1 ≈ _15.0 (parameter aliases with field of temporary variable)
                //
                // Both sides are connected through the bridge variable _15, but:
                //   1. _15 is a temporary (root > arg_count), so it won't appear in final summary
                //   2. There's no direct alias between _0.x and _1 in all_pairs
                //   3. Union-Find guarantees transitivity within all_pairs, but the connection
                //      happens at different structural levels (parent vs child fields)
                //
                // Solution: For alias pairs connected through the same bridge variable where one
                // side references the bridge's parent and the other references a child field,
                // we derive a direct alias between the parameter/return places, compressing
                // deep field paths to maintain precision while avoiding temporary variables.
                //
                // Example derivation:
                //   Input:  _0.0.0.0 ≈ _15 (place_i ≈ place_j)
                //           _1 ≈ _15.0 (place_k ≈ place_m)
                //   Check:  place_j.root (15) == place_m.root (15) ✓ (same bridge)
                //           _15 is prefix of _15.0 ✓ (parent-child relation)
                //   Output: _0.0 ≈ _1 (compress _0's deep fields to first level)
                //
                for &(idx_i, idx_j, place_i, place_j) in &all_pairs {
                    if !relevant_places.contains(&idx_i) || !relevant_places.contains(&idx_j) {
                        continue;
                    }

                    for &(idx_k, idx_m, place_k, place_m) in &all_pairs {
                        if !relevant_places.contains(&idx_k) || !relevant_places.contains(&idx_m) {
                            continue;
                        }

                        // Check if both alias pairs share the same bridge variable (by root)
                        if place_j.root_local() != place_m.root_local() {
                            continue;
                        }

                        // Extract field paths for prefix checking
                        let j_fields = extract_field_path(place_j);
                        let m_fields = extract_field_path(place_m);

                        // Verify parent-child relationship (proper prefix, not sibling fields)
                        // E.g., [] is prefix of [0], but [0] is NOT prefix of [1]
                        if !is_field_prefix(&j_fields, &m_fields)
                            && !is_field_prefix(&m_fields, &j_fields)
                        {
                            continue;
                        }

                        // Extract roots and fields from both sides
                        let (root_i, mut fields_i) = extract_fields(place_i);
                        let (root_k, fields_k) = extract_fields(place_k);

                        // Only derive aliases between parameters and return value
                        if root_i > arg_count || root_k > arg_count {
                            continue;
                        }

                        // Compress deep field paths to first level only
                        // This balances precision (distinguishing struct fields) with
                        // generality (avoiding over-specification)
                        fields_i.reverse(); // extract_fields returns reversed order
                        if fields_i.len() > 1 {
                            fields_i = vec![fields_i[0]];
                        }

                        let mut fields_k_reversed = fields_k.clone();
                        fields_k_reversed.reverse();

                        // Create the derived alias and add to candidates
                        let mut alias = AliasPair::new(root_i, root_k);
                        alias.lhs_fields = fields_i;
                        alias.rhs_fields = fields_k_reversed;

                        candidate_aliases.insert(alias);
                    }
                }

                // Step 4.2: Direct aliases from all_pairs
                //
                // Collect aliases that are directly present between parameters and return values
                // in the Union-Find analysis results. These may overlap with derived aliases from
                // Step 4.1, but duplicates are automatically handled by the HashSet.
                //
                for (idx_i, idx_j, place_i, place_j) in all_pairs {
                    if relevant_places.contains(&idx_i) && relevant_places.contains(&idx_j) {
                        let (root_i, mut fields_i) = extract_fields(place_i);
                        let (root_j, mut fields_j) = extract_fields(place_j);

                        // Only include if both roots are parameters or return value
                        if root_i <= arg_count && root_j <= arg_count {
                            // Fields were collected from leaf to root, reverse them
                            fields_i.reverse();
                            fields_j.reverse();

                            // Create field-sensitive AliasPair and add to candidates
                            let mut alias = AliasPair::new(root_i, root_j);
                            alias.lhs_fields = fields_i;
                            alias.rhs_fields = fields_j;
                            candidate_aliases.insert(alias);
                        }
                    }
                }

                // Step 5: Filter redundant aliases and add to summary
                //
                // The candidate set may contain redundant aliases such as:
                //   - Self-aliases: (0.0, 0.0), (1, 1)
                //   - Prefix-subsumed aliases: (0.0, 1) subsumes (0.0.0, 1), (0.0.0.0, 1)
                //
                // We filter these to produce a minimal, canonical summary that retains
                // precision while avoiding over-specification.
                //
                let filtered_aliases = filter_redundant_aliases(candidate_aliases);
                for alias in filtered_aliases {
                    summary.add_alias(alias);
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

/// Filter redundant aliases from a candidate set
///
/// This function removes several types of redundant aliases to produce a minimal,
/// canonical summary:
///
/// 1. **Self-aliases**: Aliases where both sides refer to the same place
///    Example: (0.0, 0.0), (1, 1)
///
/// 2. **Prefix-subsumed aliases**: When one alias is strictly more general than another
///    Example: (0.0, 1) subsumes (0.0.0, 1), (0.0.0.0, 1), etc.
///    We keep the more general (shorter field path) alias.
///
/// The filtering process:
///   - For each pair of aliases with the same (left_local, right_local):
///     - Check if one's field paths are prefixes of the other's
///     - Keep the one with shorter (more general) field paths
///   - Remove all self-aliases
///
/// Returns: A filtered HashSet containing only non-redundant aliases
fn filter_redundant_aliases(
    aliases: std::collections::HashSet<AliasPair>,
) -> std::collections::HashSet<AliasPair> {
    let mut result = aliases.clone();
    let aliases_vec: Vec<_> = aliases.iter().cloned().collect();

    for i in 0..aliases_vec.len() {
        let alias_a = &aliases_vec[i];

        // Rule 1: Remove self-aliases (same local)
        if alias_a.left_local == alias_a.right_local {
            result.remove(alias_a);
            continue;
        }

        // Rule 2: Check for prefix subsumption with other aliases
        for j in 0..aliases_vec.len() {
            if i == j {
                continue;
            }
            let alias_b = &aliases_vec[j];

            // Only compare aliases with the same locals
            if alias_a.left_local != alias_b.left_local
                || alias_a.right_local != alias_b.right_local
            {
                continue;
            }

            // Check if alias_a's fields are (strict) prefixes of alias_b's fields
            let lhs_subsumes = is_strict_prefix(&alias_a.lhs_fields, &alias_b.lhs_fields)
                || alias_a.lhs_fields == alias_b.lhs_fields;
            let rhs_subsumes = is_strict_prefix(&alias_a.rhs_fields, &alias_b.rhs_fields)
                || alias_a.rhs_fields == alias_b.rhs_fields;

            // If alias_a subsumes alias_b (at least one side is a strict prefix),
            // remove the more specific alias_b
            if lhs_subsumes && rhs_subsumes {
                // At least one side must be a strict prefix (not both equal)
                let lhs_is_strict = is_strict_prefix(&alias_a.lhs_fields, &alias_b.lhs_fields);
                let rhs_is_strict = is_strict_prefix(&alias_a.rhs_fields, &alias_b.rhs_fields);

                if lhs_is_strict || rhs_is_strict {
                    result.remove(alias_b);
                }
            }
        }
    }

    result
}

/// Check if `prefix` is a strict prefix of `full`
///
/// A strict prefix means:
///   - `prefix` is shorter than `full`
///   - All elements of `prefix` match the corresponding elements in `full`
///
/// Examples:
///   - is_strict_prefix([0], [0, 1]) = true
///   - is_strict_prefix([], [0]) = true
///   - is_strict_prefix([0], [0]) = false (equal, not strict)
///   - is_strict_prefix([0], [1]) = false (not a prefix)
fn is_strict_prefix(prefix: &[usize], full: &[usize]) -> bool {
    prefix.len() < full.len() && prefix == &full[..prefix.len()]
}
