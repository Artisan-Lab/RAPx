extern crate rustc_infer;
use crate::rap_debug;
use rustc_hir::def_id::DefId;
use rustc_infer::infer::region_constraints::Constraint;
use rustc_infer::infer::{self, InferCtxt, TyCtxtInferExt};
use rustc_infer::traits::ObligationCause;
use rustc_middle::ty::{self, TyCtxt, TypeFoldable};
use rustc_span::Span;
struct FreeVarFolder<'tcx, 'a> {
    cx: TyCtxt<'tcx>,
    free_var_cnt: usize,
    infcx: &'a InferCtxt<'tcx>,
    span: Span,
}

impl<'tcx, 'a> FreeVarFolder<'tcx, 'a> {
    pub fn new(
        cx: TyCtxt<'tcx>,
        infcx: &'a InferCtxt<'tcx>,
        span: Span,
    ) -> FreeVarFolder<'tcx, 'a> {
        FreeVarFolder {
            cx,
            free_var_cnt: 0,
            infcx,
            span,
        }
    }
}

impl<'tcx> ty::TypeFolder<TyCtxt<'tcx>> for FreeVarFolder<'tcx, '_> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.cx
    }
    fn fold_region(&mut self, _: ty::Region<'tcx>) -> ty::Region<'tcx> {
        self.free_var_cnt += 1;
        self.infcx
            .next_region_var(infer::RegionVariableOrigin::BorrowRegion(self.span))
    }
}

fn region_vid_str(vid: ty::RegionVid) -> String {
    format!("{:?}", vid)
}

fn region_str(region: ty::Region<'_>) -> String {
    region.get_name_or_anon().to_string()
}

fn constraint_str<'tcx>(constraint: Constraint<'tcx>, tcx: TyCtxt<'tcx>) -> String {
    let (a, b) = match constraint {
        Constraint::VarSubVar(a, b) => (region_vid_str(a), region_vid_str(b)),
        Constraint::RegSubVar(a, b) => (region_str(a), region_vid_str(b)),
        Constraint::VarSubReg(a, b) => (region_vid_str(a), region_str(b)),
        Constraint::RegSubReg(a, b) => (region_str(a), region_str(b)),
    };
    format!("{} <= {}", a, b)
}

pub fn extract_constraints(fn_did: DefId, tcx: TyCtxt<'_>) {
    let early_fn_sig = tcx.fn_sig(fn_did);
    let span = tcx.def_span(fn_did);
    let binder_fn_sig = early_fn_sig.instantiate_identity();

    let param_env = tcx.param_env(fn_did);
    rap_debug!("param_env: {param_env:?}");

    // obtain subtyping contraints
    let infcx = tcx.infer_ctxt().build();
    let mut folder = FreeVarFolder::new(tcx, &infcx, span);
    let fn_sig = tcx.liberate_late_bound_regions(fn_did, binder_fn_sig);
    let binder_with_free_vars = fn_sig.fold_with(&mut folder);

    let res = infcx
        .at(&ObligationCause::dummy(), param_env)
        .sub(infer::DefineOpaqueTypes::Yes, fn_sig, binder_with_free_vars)
        .unwrap();
    res.obligations.into_iter().for_each(|obligation| {
        rap_debug!("obligation: {obligation:?}");
    });

    // rap_debug!("binder: {binder_with_vars:?}");
    rap_debug!("free binder: {binder_with_free_vars:?}");
    let region_constraint_data = infcx.take_and_reset_region_constraints();
    for (constraint, origin) in region_constraint_data.constraints {
        rap_debug!("constraint: {}", constraint_str(constraint, tcx));
    }
}
