use rustc_middle::mir::pretty::{write_mir_fn, PrettyPrintMirOptions};
use std::collections::HashMap;
#[allow(unused)]
use std::collections::HashSet;
use std::io::Cursor;
// use std::fs::File;
// use std::io::{self, Write};
// use rustc_index::bit_set::BitSet;
// use rustc_index::IndexSlice;
// use rustc_middle::mir::visit::Visitor;
// use rustc_middle::mir::visit::*;
// use rustc_middle::mir::visit::*;
// use rustc_middle::mir::visit::*;
use rustc_middle::mir::*;
// use rustc_middle::mir::{visit::MutVisitor, Body};
use crate::{rap_info, rap_warn};
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
    pub fn get_final_ssa_as_string(&self, body: &Body<'tcx>) -> String {
        // origin_mir
        // let mut buffer1 = Cursor::new(Vec::new());
        // write_mir_pretty(self.tcx, None, &mut buffer1).unwrap();
        // let origin_mir = String::from_utf8(buffer1.into_inner()).unwrap();
        // after_rename_mir
        let mut buffer2 = Cursor::new(Vec::new());
        let options = PrettyPrintMirOptions::from_cli(self.tcx);
        write_mir_fn(self.tcx, body, &mut |_, _| Ok(()), &mut buffer2, options).unwrap();
        let after_mir = String::from_utf8(buffer2.into_inner()).unwrap();
        after_mir
    }
    pub fn lvalue_check(mir_string: &str) -> bool {
        let re = regex::Regex::new(r"_(\d+)\s*=").unwrap();
        let mut counts = HashMap::new();
        let mut has_duplicate = false;

        for cap in re.captures_iter(mir_string) {
            let var = cap[1].parse::<u32>().unwrap();
            let counter = counts.entry(var).or_insert(0);
            *counter += 1;
            if *counter > 1 {
                has_duplicate = true;
            }
        }

        for (var, count) in counts {
            if count > 1 {
                rap_warn!("Variable _{} is used {} times", var, count);
            }
        }

        !has_duplicate
    }
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
        let essa_mir_string = self.get_final_ssa_as_string(body);
        rap_info!("final SSA {:?}\n", &essa_mir_string);
        rap_info!(
            "ssa lvalue check true{:?}",
            PassRunner::lvalue_check(&essa_mir_string)
        );
    }
}
