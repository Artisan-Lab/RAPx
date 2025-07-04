#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_assignments)]
#![allow(unused_parens)]
#![allow(non_snake_case)]
use crate::{rap_info, rap_warn};

use super::SSA::SSATransformer::SSATransformer;
use rustc_hir::def_id::DefId;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::pretty::{write_mir_fn, PrettyPrintMirOptions};
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use std::fs::File;
use std::io;
use std::io::Cursor;
use std::io::Write;
use std::path::PathBuf;

use super::SSA::Replacer::*;
pub struct PassRunner<'tcx> {
    tcx: TyCtxt<'tcx>,
    pub places_map: HashMap<Place<'tcx>, HashSet<Place<'tcx>>>,
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
            rap_warn!("Variable _ {} is used {} times", var, count);
        }
    }

    !has_duplicate
}
pub fn print_diff<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, def_id: DefId) {
    let dir_path = "passrunner_mir";
    fs::create_dir_all(dir_path).unwrap();
    // PassRunner::new(self.tcx);
    let name = tcx.def_path_str(def_id);
    let mir_file_path = format!("{}/origin_mir.txt", dir_path);
    let phi_mir_file_path = format!("{}/{}_after_rename_mir.txt", dir_path, name);
    let mut file = File::create(&mir_file_path).unwrap();
    let mut w = io::BufWriter::new(&mut file);
    write_mir_pretty(tcx, None, &mut w).unwrap();
    let mut file2 = File::create(&phi_mir_file_path).unwrap();
    let mut w2 = io::BufWriter::new(&mut file2);
    let options = PrettyPrintMirOptions::from_cli(tcx);
    write_mir_fn(tcx, body, &mut |_, _| Ok(()), &mut w2, options).unwrap();
}
pub fn print_mir_graph<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, def_id: DefId) {
    let dir_path = PathBuf::from("passrunner_mir_dot");
    fs::create_dir_all(dir_path.clone()).unwrap();

    let dot_graph = mir_to_dot(tcx, body);
    let function_name = tcx.def_path_str(def_id);
    let safe_filename = format!("{}_after_rename_mir.dot", function_name);
    let output_path = dir_path.join(format!("{}", safe_filename));

    let mut file = File::create(&output_path).expect("cannot create file");
    let _ = file.write_all(dot_graph.as_bytes());
}
fn mir_to_dot<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> String {
    let mut dot = String::new();
    dot.push_str("digraph MIR {\n");
    dot.push_str("  node [shape=box];\n");

    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        let statements_str = bb_data
            .statements
            .iter()
            .map(|stmt| format!("{:?}", stmt).replace('\n', " "))
            .collect::<Vec<_>>()
            .join("\\l");

        dot.push_str(&format!(
            "  {} [label=\"{:?}:\\l{}\\l\"];\n",
            bb.index(),
            bb,
            statements_str
        ));
        if let Some(terminator) = &bb_data.terminator {
            for successor in terminator.successors() {
                dot.push_str(&format!("  {} -> {};\n", bb.index(), successor.index()));
            }
        }
    }

    dot.push_str("}\n");
    dot
}
impl<'tcx> PassRunner<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            places_map: HashMap::default(),
        }
    }

    pub fn get_final_ssa_as_string(&self, body: &Body<'tcx>) -> String {
        let mut buffer2 = Cursor::new(Vec::new());
        let options = PrettyPrintMirOptions::from_cli(self.tcx);
        write_mir_fn(self.tcx, body, &mut |_, _| Ok(()), &mut buffer2, options).unwrap();
        let after_mir = String::from_utf8(buffer2.into_inner()).unwrap();
        after_mir
    }

    pub fn run_pass(&mut self, body: &mut Body<'tcx>, ssa_def_id: DefId, essa_def_id: DefId) {
        let arg_count = body.arg_count;
        let ssatransformer =
            SSATransformer::new(self.tcx, body, ssa_def_id, essa_def_id, arg_count);
        ssatransformer.print_ssatransformer();
        let mut replacer = Replacer {
            tcx: self.tcx,
            ssatransformer,
            new_local_collection: HashSet::default(),
        };
        replacer.insert_phi_statment(body);
        replacer.insert_essa_statement(body);
        replacer.rename_variables(body);
        self.places_map = replacer.ssatransformer.places_map.clone();
    }
}
