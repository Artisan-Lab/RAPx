#![feature(rustc_private)]
#![feature(box_patterns)]

#[macro_use]
pub mod utils;
pub mod analysis;

extern crate intervals;
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate stable_mir;

use crate::analysis::core::heap_item::TypeAnalysis;
use analysis::core::alias::mop::MopAlias;
use analysis::core::api_dep::ApiDep;
use analysis::core::call_graph::CallGraph;
use analysis::core::dataflow::DataFlow;
use analysis::core::range_analysis::{RangeAnalysis, SSATrans};
use analysis::opt::Opt;
use analysis::rcanary::rCanary;
use analysis::safedrop::SafeDrop;
use analysis::senryx::{CheckLevel, SenryxCheck};
use analysis::unsafety_isolation::{UigInstruction, UnsafetyIsolationCheck};
use analysis::utils::show_mir::ShowMir;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_interface::Config;
use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;
use rustc_session::search_paths::PathKind;
use std::path::PathBuf;
use std::{env, sync::Arc};

// Insert rustc arguments at the beginning of the argument list that RAP wants to be
// set per default, for maximal validation power.
pub static RAP_DEFAULT_ARGS: &[&str] = &["-Zalways-encode-mir", "-Zmir-opt-level=0"];

pub type Elapsed = (i64, i64);

#[derive(Debug, Copy, Clone, Hash)]
pub struct RapCallback {
    rcanary: bool,
    safedrop: bool,
    verify: bool,
    infer: bool,
    unsafety_isolation: usize,
    mop: bool,
    callgraph: bool,
    api_dep: bool,
    show_mir: bool,
    dataflow: usize,
    opt: usize,
    heap_item: bool,
    ssa: bool,
    range: bool,
}

#[allow(clippy::derivable_impls)]
impl Default for RapCallback {
    fn default() -> Self {
        Self {
            rcanary: false,
            safedrop: false,
            verify: false,
            infer: false,
            unsafety_isolation: 0,
            mop: false,
            callgraph: false,
            api_dep: false,
            show_mir: false,
            dataflow: 0,
            opt: usize::MAX,
            heap_item: false,
            ssa: false,
            range: false,
        }
    }
}

impl Callbacks for RapCallback {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_, providers| {
            providers.extern_queries.used_crate_source = |tcx, cnum| {
                let mut providers = Providers::default();
                rustc_metadata::provide(&mut providers);
                let mut crate_source = (providers.extern_queries.used_crate_source)(tcx, cnum);
                // HACK: rustc will emit "crate ... required to be available in rlib format, but
                // was not found in this form" errors once we use `tcx.dependency_formats()` if
                // there's no rlib provided, so setting a dummy path here to workaround those errors.
                Arc::make_mut(&mut crate_source).rlib = Some((PathBuf::new(), PathKind::All));
                crate_source
            };
        });
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        rap_trace!("Execute after_analysis() of compiler callbacks");
        start_analyzer(tcx, *self);
        rap_trace!("analysis done");
        Compilation::Continue
    }
}

impl RapCallback {
    pub fn enable_rcanary(&mut self) {
        self.rcanary = true;
    }

    pub fn is_rcanary_enabled(&self) -> bool {
        self.rcanary
    }

    pub fn enable_mop(&mut self, arg: String) {
        self.mop = true;
        match arg.as_str() {
            "-alias" => {
                env::set_var("MOP", "1");
            }
            "-alias0" => {
                env::set_var("MOP", "0");
            }
            "-alias1" => {
                env::set_var("MOP", "1");
            }
            "-alias2" => {
                env::set_var("MOP", "2");
            }
            _ => {}
        }
    }

    pub fn is_mop_enabled(&self) -> bool {
        self.mop
    }

    pub fn enable_safedrop(&mut self, arg: String) {
        self.safedrop = true;
        match arg.as_str() {
            "-F" => {
                env::set_var("SAFEDROP", "1");
                env::set_var("MOP", "1");
            }
            "-F0" => {
                env::set_var("SAFEDROP", "0");
                env::set_var("MOP", "0");
            }
            "-F1" => {
                env::set_var("SAFEDROP", "1");
                env::set_var("MOP", "1");
            }
            "-F2" => {
                env::set_var("SAFEDROP", "2");
                env::set_var("MOP", "2");
            }
            "-uaf" => {
                env::set_var("SAFEDROP", "1");
                env::set_var("MOP", "1");
            }
            _ => {}
        }
    }

    pub fn is_safedrop_enabled(&self) -> bool {
        self.safedrop
    }

    pub fn enable_unsafety_isolation(&mut self, x: usize) {
        self.unsafety_isolation = x;
    }

    pub fn is_unsafety_isolation_enabled(&self) -> usize {
        self.unsafety_isolation
    }

    pub fn enable_api_dep(&mut self) {
        self.api_dep = true;
    }

    pub fn is_api_dep_enabled(self) -> bool {
        self.api_dep
    }

    pub fn enable_verify(&mut self) {
        self.verify = true;
    }

    pub fn is_verify_enabled(&self) -> bool {
        self.verify
    }

    pub fn enable_infer(&mut self) {
        self.infer = true;
    }

    pub fn is_infer_enabled(&self) -> bool {
        self.infer
    }

    pub fn enable_callgraph(&mut self) {
        self.callgraph = true;
    }

    pub fn is_callgraph_enabled(&self) -> bool {
        self.callgraph
    }

    pub fn enable_show_mir(&mut self) {
        self.show_mir = true;
    }

    pub fn is_show_mir_enabled(&self) -> bool {
        self.show_mir
    }

    pub fn enable_dataflow(&mut self, x: usize) {
        self.dataflow = x;
    }

    pub fn is_dataflow_enabled(self) -> usize {
        self.dataflow
    }

    pub fn enable_opt(&mut self, x: usize) {
        self.opt = x;
    }

    pub fn is_opt_enabled(self) -> usize {
        self.opt
    }

    pub fn enable_heap_item(&mut self) {
        self.heap_item = true;
    }

    pub fn is_heap_item_enabled(self) -> bool {
        self.heap_item
    }
    pub fn enable_ssa_transform(&mut self) {
        self.ssa = true;
    }
    pub fn is_ssa_transform_enabled(self) -> bool {
        self.ssa
    }
    pub fn enable_range_analysis(&mut self) {
        self.range = true;
    }
    pub fn is_range_analysis_enabled(self) -> bool {
        self.range
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum RapPhase {
    Cleanup,
    Cargo,
    Rustc,
    LLVM, // unimplemented yet
}

pub fn start_analyzer(tcx: TyCtxt, callback: RapCallback) {
    let _rcanary: Option<rCanary> = if callback.is_rcanary_enabled() {
        let mut rcx = rCanary::new(tcx);
        rcx.start();
        Some(rcx)
    } else {
        None
    };

    if callback.is_mop_enabled() {
        MopAlias::new(tcx).start();
    }

    if callback.is_safedrop_enabled() {
        SafeDrop::new(tcx).start();
    }

    if callback.is_heap_item_enabled() {
        let rcx_boxed = Box::new(rCanary::new(tcx));
        let rcx = Box::leak(rcx_boxed);
        let mut type_analysis = TypeAnalysis::new(rcx);
        type_analysis.start();
        type_analysis.output();
    }

    let x = callback.is_unsafety_isolation_enabled();
    match x {
        1 => UnsafetyIsolationCheck::new(tcx).start(UigInstruction::StdSp),
        2 => UnsafetyIsolationCheck::new(tcx).start(UigInstruction::Doc),
        3 => UnsafetyIsolationCheck::new(tcx).start(UigInstruction::Upg),
        4 => UnsafetyIsolationCheck::new(tcx).start(UigInstruction::Ucons),
        _ => {}
    }

    if callback.is_verify_enabled() {
        let check_level = CheckLevel::Medium;
        SenryxCheck::new(tcx, 2).start(check_level, true);
    }

    if callback.is_infer_enabled() {
        let check_level = CheckLevel::Medium;
        SenryxCheck::new(tcx, 2).start(check_level, false);
    }

    if callback.is_show_mir_enabled() {
        ShowMir::new(tcx).start();
    }

    if callback.is_api_dep_enabled() {
        ApiDep::new(tcx).start();
    }

    match callback.is_dataflow_enabled() {
        1 => DataFlow::new(tcx, false).start(),
        2 => DataFlow::new(tcx, true).start(),
        _ => {}
    }

    if callback.is_callgraph_enabled() {
        CallGraph::new(tcx).start();
    }

    match callback.is_opt_enabled() {
        0 => Opt::new(tcx, 0).start(),
        1 => Opt::new(tcx, 1).start(),
        2 => Opt::new(tcx, 2).start(),
        _ => {}
    }
    if callback.is_ssa_transform_enabled() {
        SSATrans::new(tcx, false).start();
    }
    if callback.is_range_analysis_enabled() {
        RangeAnalysis::new(tcx, false).start();
    }
}
