#[allow(unused)]
pub mod contracts;
#[allow(unused)]
pub mod dominated_graph;
pub mod generic_check;
// pub mod inter_record;
pub mod matcher;
pub mod symbolic_analysis;
#[allow(unused)]
pub mod visitor;
#[allow(unused)]
pub mod visitor_check;
use dominated_graph::InterResultNode;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::{
    mir::{BasicBlock, Operand, TerminatorKind},
    ty::{self, TyCtxt},
};
use std::collections::HashSet;
use visitor::{BodyVisitor, CheckResult};

use crate::analysis::{
    Analysis,
    core::alias_analysis::{AAResult, AliasAnalysis, default::AliasAnalyzer},
    upg::{fn_collector::FnCollector, hir_visitor::ContainsUnsafe},
    utils::fn_info::*,
};

macro_rules! cond_print {
    ($cond:expr, $($t:tt)*) => {if $cond {rap_warn!($($t)*)} else {rap_info!($($t)*)}};
}

pub enum CheckLevel {
    High,
    Medium,
    Low,
}

pub struct SenryxCheck<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub threshhold: usize,
}

impl<'tcx> SenryxCheck<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, threshhold: usize) -> Self {
        Self { tcx, threshhold }
    }

    pub fn start(&mut self, check_level: CheckLevel, is_verify: bool) {
        let tcx = self.tcx;
        let mut analyzer = AliasAnalyzer::new(self.tcx);
        analyzer.run();
        let fn_map = &analyzer.get_all_fn_alias();
        let related_items = FnCollector::collect(tcx);
        for vec in related_items.clone().values() {
            for (body_id, _span) in vec {
                let (function_unsafe, block_unsafe) =
                    ContainsUnsafe::contains_unsafe(tcx, *body_id);
                let def_id = tcx.hir_body_owner_def_id(*body_id).to_def_id();
                let std_unsafe_callee = get_all_std_unsafe_callees(self.tcx, def_id);
                if !Self::filter_by_check_level(tcx, &check_level, def_id) {
                    continue;
                }
                if block_unsafe && is_verify && !std_unsafe_callee.is_empty() {
                    self.check_soundness(def_id, fn_map);
                }
                if function_unsafe && !is_verify && !std_unsafe_callee.is_empty() {
                    // self.annotate_safety(def_id);
                    // let mutable_methods = get_all_mutable_methods(self.tcx, def_id);
                    // println!("mutable_methods: {:?}", mutable_methods);
                }
            }
        }
    }

    pub fn start_analyze_std_func(&mut self) {
        let v_fn_def: Vec<_> = rustc_public::find_crates("alloc")
            .iter()
            .flat_map(|krate| krate.fn_defs())
            .collect();
        for fn_def in &v_fn_def {
            let def_id = crate::def_id::to_internal(fn_def, self.tcx);
            if is_verify_target_func(self.tcx, def_id) {
                rap_info!(
                    "Begin verification process for: {:?}",
                    get_cleaned_def_path_name(self.tcx, def_id)
                );
                let check_results = self.body_visit_and_check(def_id, &FxHashMap::default());
                if !check_results.is_empty() {
                    Self::show_check_results(self.tcx, def_id, check_results);
                }
            }
        }
    }

    pub fn start_analyze_std_func_chains(&mut self) {
        let all_std_fn_def = get_all_std_fns_by_rustc_public(self.tcx);
        let mut last_nodes = HashSet::new();
        for &def_id in &all_std_fn_def {
            if !check_visibility(self.tcx, def_id) {
                continue;
            }
            let chains = get_all_std_unsafe_chains(self.tcx, def_id);
            let valid_chains: Vec<Vec<String>> = chains
                .into_iter()
                .filter(|chain| {
                    if chain.len() > 1 {
                        return true;
                    }
                    if chain.len() == 1 {
                        if check_safety(self.tcx, def_id) == Safety::Unsafe {
                            return true;
                        }
                    }
                    false
                })
                .collect();

            let mut last = true;
            for chain in &valid_chains {
                if let Some(last_node) = chain.last() {
                    if !last_node.contains("intrinsic") && !last_node.contains("aarch64") {
                        last_nodes.insert(last_node.clone());
                        last = false;
                    }
                }
            }
            if last {
                continue;
            }
            // print_unsafe_chains(&valid_chains);
        }
        Self::print_last_nodes(&last_nodes);
    }

    pub fn print_last_nodes(last_nodes: &HashSet<String>) {
        if last_nodes.is_empty() {
            println!("No unsafe call chain last nodes found.");
            return;
        }

        println!(
            "Found {} unique unsafe call chain last nodes:",
            last_nodes.len()
        );
        for (i, node) in last_nodes.iter().enumerate() {
            println!("{}. {}", i + 1, node);
        }
    }

    pub fn filter_by_check_level(
        tcx: TyCtxt<'tcx>,
        check_level: &CheckLevel,
        def_id: DefId,
    ) -> bool {
        match *check_level {
            CheckLevel::High => check_visibility(tcx, def_id),
            _ => true,
        }
    }

    pub fn check_soundness(&mut self, def_id: DefId, fn_map: &FxHashMap<DefId, AAResult>) {
        let check_results = self.body_visit_and_check(def_id, fn_map);
        let tcx = self.tcx;
        if !check_results.is_empty() {
            Self::show_check_results(tcx, def_id, check_results);
        }
    }

    pub fn annotate_safety(&self, def_id: DefId) {
        let annotation_results = self.get_annotation(def_id);
        if annotation_results.is_empty() {
            return;
        }
        Self::show_annotate_results(self.tcx, def_id, annotation_results);
    }

    pub fn body_visit_and_check(
        &mut self,
        def_id: DefId,
        fn_map: &FxHashMap<DefId, AAResult>,
    ) -> Vec<CheckResult> {
        let mut body_visitor = BodyVisitor::new(self.tcx, def_id, 0);
        let target_name = get_cleaned_def_path_name(self.tcx, def_id);
        rap_info!("Begin verification process for: {:?}", target_name);
        if get_type(self.tcx, def_id) == FnKind::Method {
            let cons = get_cons(self.tcx, def_id);
            let mut base_inter_result = InterResultNode::new_default(get_adt_ty(self.tcx, def_id));
            for con in cons {
                let mut cons_body_visitor = BodyVisitor::new(self.tcx, con, 0);
                let cons_fields_result = cons_body_visitor.path_forward_check(fn_map);
                // cache and merge fields' states
                let cons_name = get_cleaned_def_path_name(self.tcx, con);
                println!(
                    "cons {cons_name} state results {:?}",
                    cons_fields_result.clone()
                );
                base_inter_result.merge(cons_fields_result);
            }
            // update method body's states by constructors' states
            body_visitor.update_fields_states(base_inter_result);
            // get mutable methods and TODO: update target method's states
            let mutable_methods = get_all_mutable_methods(self.tcx, def_id);
            for mm in mutable_methods {
                println!("mut method {:?}", get_cleaned_def_path_name(self.tcx, mm.0));
                // has_tainted_fields(self.tcx, mm.0, 1);
            }
            // analyze body's states
            body_visitor.path_forward_check(fn_map);
        } else {
            body_visitor.path_forward_check(fn_map);
        }
        body_visitor.check_results
    }

    pub fn body_visit_and_check_uig(&self, def_id: DefId) {
        let func_type = get_type(self.tcx, def_id);
        if func_type == FnKind::Method && !self.get_annotation(def_id).is_empty() {
            let func_cons = search_constructor(self.tcx, def_id);
            for func_con in func_cons {
                if check_safety(self.tcx, func_con) == Safety::Unsafe {
                    Self::show_annotate_results(self.tcx, func_con, self.get_annotation(def_id));
                    // uphold safety to unsafe constructor
                }
            }
        }
    }

    pub fn get_annotation(&self, def_id: DefId) -> HashSet<String> {
        let mut results = HashSet::new();
        if !self.tcx.is_mir_available(def_id) {
            return results;
        }
        let body = self.tcx.optimized_mir(def_id);
        let basicblocks = &body.basic_blocks;
        for i in 0..basicblocks.len() {
            let iter = BasicBlock::from(i);
            let terminator = basicblocks[iter].terminator.clone().unwrap();
            if let TerminatorKind::Call {
                ref func,
                args: _,
                destination: _,
                target: _,
                unwind: _,
                call_source: _,
                fn_span: _,
            } = terminator.kind
            {
                match func {
                    Operand::Constant(c) => {
                        if let ty::FnDef(id, ..) = c.ty().kind() {
                            if !get_sp(self.tcx, *id).is_empty() {
                                results.extend(get_sp(self.tcx, *id));
                            } else {
                                results.extend(self.get_annotation(*id));
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        results
    }

    pub fn show_check_results(tcx: TyCtxt<'tcx>, def_id: DefId, check_results: Vec<CheckResult>) {
        rap_info!(
            "--------In safe function {:?}---------",
            get_cleaned_def_path_name(tcx, def_id)
        );
        for check_result in &check_results {
            // Aggregate all failed contracts from all arguments
            let mut all_failed = HashSet::new();
            for set in check_result.failed_contracts.values() {
                for sp in set {
                    all_failed.insert(sp);
                }
            }

            // Aggregate all passed contracts from all arguments
            let mut all_passed = HashSet::new();
            for set in check_result.passed_contracts.values() {
                for sp in set {
                    all_passed.insert(sp);
                }
            }

            // Print the API name with conditional coloring
            cond_print!(
                !all_failed.is_empty(),
                "  Use unsafe api {:?}.",
                check_result.func_name
            );

            // Print aggregated Failed set
            if !all_failed.is_empty() {
                let mut failed_sorted: Vec<&String> = all_failed.into_iter().collect();
                failed_sorted.sort();
                cond_print!(true, "      Failed: {:?}", failed_sorted);
            }

            // Print aggregated Passed set
            if !all_passed.is_empty() {
                let mut passed_sorted: Vec<&String> = all_passed.into_iter().collect();
                passed_sorted.sort();
                cond_print!(false, "      Passed: {:?}", passed_sorted);
            }
        }
    }

    pub fn show_annotate_results(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        annotation_results: HashSet<String>,
    ) {
        rap_info!(
            "--------In unsafe function {:?}---------",
            get_cleaned_def_path_name(tcx, def_id)
        );
        rap_warn!("Lack safety annotations: {:?}.", annotation_results);
    }
}
