#![allow(non_snake_case)]
use crate::rap_info;

pub mod PassRunner;
pub mod SSA;
pub mod domain;
use domain::ConstraintGraph::ConstraintGraph;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::Body;
use rustc_middle::ty::TyCtxt;
use PassRunner::*;
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
                if self.tcx.hir_maybe_body_owned_by(local_def_id).is_some() {
                    if let Some(def_id) = self
                        .tcx
                        .hir_body_owners()
                        .find(|id| self.tcx.def_path_str(*id) == "main")
                    {
                        if let Some(ssa_def_id) =
                            self.tcx.hir_crate_items(()).free_items().find(|id| {
                                let hir_id = id.hir_id();
                                if let Some(ident_name) = self.tcx.hir_opt_name(hir_id) {
                                    ident_name.to_string() == "SSAstmt"
                                } else {
                                    false
                                }
                            })
                        {
                            let ssa_def_id = ssa_def_id.owner_id.to_def_id();
                            if let Some(essa_def_id) =
                                self.tcx.hir_crate_items(()).free_items().find(|id| {
                                    let hir_id = id.hir_id();
                                    if let Some(ident_name) = self.tcx.hir_opt_name(hir_id) {
                                        ident_name.to_string() == "ESSAstmt"
                                    } else {
                                        false
                                    }
                                })
                            {
                                let essa_def_id = essa_def_id.owner_id.to_def_id();
                                self.analyze_mir(self.tcx, def_id, ssa_def_id, essa_def_id);
                            }
                        }
                    }
                }
            }
        }
    }
    fn analyze_mir(
        &mut self,
        tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
        ssa_def_id: DefId,
        essa_def_id: DefId,
    ) {
        let mut body = tcx.optimized_mir(def_id).clone();
        {
            let body_mut_ref: &mut Body<'tcx> = unsafe { &mut *(&mut body as *mut Body<'tcx>) };
            let passrunner = PassRunner::PassRunner::new(tcx);
            passrunner.run_pass(body_mut_ref, ssa_def_id, essa_def_id);
            // passrunner.print_diff(body_mut_ref);
            let essa_mir_string = passrunner.get_final_ssa_as_string(body_mut_ref);

            // rap_info!("final SSA {:?}\n", &essa_mir_string);
            rap_info!("ssa lvalue check {:?}", lvalue_check(&essa_mir_string));
        }
    }
}
pub struct RangeAnalysis<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub debug: bool,
}
impl<'tcx> RangeAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, debug: bool) -> Self {
        Self { tcx: tcx, debug }
    }

    pub fn start(&mut self) {
        for local_def_id in self.tcx.iter_local_def_id() {
            if matches!(self.tcx.def_kind(local_def_id), DefKind::Fn) {
                if self.tcx.hir_maybe_body_owned_by(local_def_id).is_some() {
                    if let Some(def_id) = self
                        .tcx
                        .hir_body_owners()
                        .find(|id| self.tcx.def_path_str(*id) == "main")
                    {
                        if let Some(ssa_def_id) =
                            self.tcx.hir_crate_items(()).free_items().find(|id| {
                                let hir_id = id.hir_id();
                                if let Some(ident_name) = self.tcx.hir_opt_name(hir_id) {
                                    ident_name.to_string() == "SSAstmt"
                                } else {
                                    false
                                }
                            })
                        {
                            let ssa_def_id = ssa_def_id.owner_id.to_def_id();
                            if let Some(essa_def_id) =
                                self.tcx.hir_crate_items(()).free_items().find(|id| {
                                    let hir_id = id.hir_id();
                                    if let Some(ident_name) = self.tcx.hir_opt_name(hir_id) {
                                        ident_name.to_string() == "ESSAstmt"
                                    } else {
                                        false
                                    }
                                })
                            {
                                let essa_def_id = essa_def_id.owner_id.to_def_id();
                                self.analyze_mir(self.tcx, def_id, ssa_def_id, essa_def_id);
                            }
                        }
                    }
                }
            }
        }
    }
    fn analyze_mir(
        &mut self,
        tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
        ssa_def_id: DefId,
        essa_def_id: DefId,
    ) {
        let mut body = tcx.optimized_mir(def_id).clone();
        {
            let body_mut_ref: &mut Body<'tcx> = unsafe { &mut *(&mut body as *mut Body<'tcx>) };
            let passrunner = PassRunner::PassRunner::new(tcx);
            passrunner.run_pass(body_mut_ref, ssa_def_id, essa_def_id);
            // print_diff(tcx, body_mut_ref);
            let mut cg: ConstraintGraph<'tcx, u32> = ConstraintGraph::new(essa_def_id, ssa_def_id);
            cg.build_graph(body_mut_ref);
            cg.build_nuutila(false);
            cg.find_intervals();
            cg.print_vars();
        }
    }
}
