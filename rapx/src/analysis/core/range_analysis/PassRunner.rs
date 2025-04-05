use std::collections::HashSet;
use std::fs::File;
use std::io::{self, Write};

use rustc_index::bit_set::BitSet;
use rustc_index::IndexSlice;
use rustc_middle::mir::pretty::{write_mir_fn, PrettyPrintMirOptions};
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::visit::*;
use rustc_middle::mir::visit::*;
use rustc_middle::mir::visit::*;
use rustc_middle::mir::*;
use rustc_middle::mir::*;
use rustc_middle::mir::{visit::MutVisitor, Body};
use rustc_middle::ty::TyCtxt;
// use crate::domain::ConstraintGraph::ConstraintGraph;
use super::SSA::SSATransformer::SSATransformer;

use super::SSA::Replacer::*;
pub struct PassRunner<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> PassRunner<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }
    // pub fn print_diff(&self, body: &Body<'tcx>) {
    //     let dir_path = "passrunner_mir";
    //     // PassRunner::new(self.tcx);
    //     // 动态生成文件路径
    //     let mir_file_path = format!("{}/origin_mir.txt", dir_path);
    //     let phi_mir_file_path = format!("{}/after_rename_mir.txt", dir_path);
    //     let mut file = File::create(&mir_file_path).unwrap();
    //     let mut w = io::BufWriter::new(&mut file);
    //     write_mir_pretty(self.tcx, None, &mut w).unwrap();
    //     let mut file2 = File::create(&phi_mir_file_path).unwrap();
    //     let mut w2 = io::BufWriter::new(&mut file2);
    //     let options = PrettyPrintMirOptions::from_cli(self.tcx);
    //     write_mir_fn(self.tcx, body, &mut |_, _| Ok(()), &mut w2, options).unwrap();
    // }
    pub fn run_pass(&self, body: &mut Body<'tcx>) {
        let ssatransformer =
            SSATransformer::new(self.tcx, body, body.source.def_id().expect_local());
        let mut replacer = Replacer {
            tcx: self.tcx,

            ssatransformer,
            new_local_collection: HashSet::default(),
        };
        replacer.insert_phi_statment(body);
        replacer.insert_essa_statement(body);
        replacer.rename_variables(body);
    }
}
