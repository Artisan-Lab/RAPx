#![allow(non_snake_case)]

pub mod PassRunner;
pub mod SSA;
use rustc_hir::def::DefKind;
use rustc_middle::mir::Body;
use rustc_middle::ty::TyCtxt;
// use std::collections::HashMap;
// use std::fs::File;
// use std::io::Write;
// use std::process::Command;
pub struct SSATrans<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub debug: bool,
}

impl<'tcx> SSATrans<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, debug: bool) -> Self {
        Self { tcx: tcx, debug }
    }

    pub fn start(&mut self) {
        for local_def_id in self.tcx.iter_local_def_id() {
            if matches!(self.tcx.def_kind(local_def_id), DefKind::Fn) {
                let hir_map = self.tcx.hir();
                if hir_map.maybe_body_owned_by(local_def_id).is_some() {
                    let def_id = local_def_id.to_def_id();
                    let mut body: Body<'tcx> = self.tcx.optimized_mir(def_id).clone();
                    let body_mut_ref = &mut body;
                    let passrunner = PassRunner::PassRunner::new(self.tcx);
                    passrunner.run_pass(body_mut_ref);

                    // // passrunner.print_diff(body_mut_ref);
                    // const body_clone  = body.clone();
                    // // let body_clone :Body<'a>=body_mut_ref.clone();
                    // let mut cg: ConstraintGraph< u32> = ConstraintGraph::new();
                    // cg.build_graph(&body);
                }
            }
        }
    }
}
// pub struct RangeAnalyzer<'tcx> {
//     pub tcx: TyCtxt<'tcx>,
//     pub debug: bool,
// }

// impl<'tcx> RangeAnalyzer<'tcx> {
//     pub fn new(tcx: TyCtxt<'tcx>, debug: bool) -> Self {
//         Self { tcx: tcx, debug }
//     }

//     pub fn start(&mut self) {
//         for local_def_id in self.tcx.iter_local_def_id() {
//             if matches!(self.tcx.def_kind(local_def_id), DefKind::Fn) {
//                 let hir_map = self.tcx.hir();
//                 if hir_map.maybe_body_owned_by(local_def_id).is_some() {
//                     let def_id = local_def_id.to_def_id();
//                     let mut body: Body<'tcx> = self.tcx.optimized_mir(def_id).clone();
//                     let body_mut_ref = &mut body;
//                     let passrunner = PassRunner::PassRunner::new(self.tcx);
//                     passrunner.run_pass(body_mut_ref);

//                     // // passrunner.print_diff(body_mut_ref);
//                     // const body_clone  = body.clone();
//                     // // let body_clone :Body<'a>=body_mut_ref.clone();
//                     // let mut cg: ConstraintGraph< u32> = ConstraintGraph::new();
//                     // cg.build_graph(&body);
//                 }
//             }
//         }
//     }
// }
