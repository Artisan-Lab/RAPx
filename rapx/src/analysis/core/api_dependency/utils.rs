#![allow(warnings, unused)]

use rustc_hir::LangItem;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, FnSig, Ty, TyCtxt, TyKind};
use rustc_span::sym;

fn is_fuzzable_std_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    match ty.kind() {
        ty::Adt(def, _) => {
            tcx.is_lang_item(def.did(), LangItem::String)
                || tcx.is_diagnostic_item(sym::Vec, def.did())
                || tcx.is_diagnostic_item(sym::Arc, def.did())
        }
        _ => false,
    }
}

pub fn is_fuzzable_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    if is_fuzzable_std_ty(ty, tcx) {
        return true;
    }

    match ty.kind() {
        // Basical data type
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Str => true,

        // Infer
        TyKind::Infer(
            ty::InferTy::IntVar(_)
            | ty::InferTy::FreshIntTy(_)
            | ty::InferTy::FloatVar(_)
            | ty::InferTy::FreshFloatTy(_),
        ) => true,

        // Reference, Array, Slice
        TyKind::Ref(_, inner_ty, _) | TyKind::Array(inner_ty, _) | TyKind::Slice(inner_ty) => {
            is_fuzzable_ty(inner_ty.peel_refs(), tcx)
        }

        // Tuple
        TyKind::Tuple(tys) => tys
            .iter()
            .all(|inner_ty| is_fuzzable_ty(inner_ty.peel_refs(), tcx)),

        // ADT
        TyKind::Adt(adt_def, substs) => {
            if adt_def.variant_list_has_applicable_non_exhaustive() {
                return false;
            }
            if adt_def.is_struct() {
                // 检查所有字段是否为 pub 且类型可 Fuzz
                adt_def.all_fields().all(|field| {
                    field.vis.is_public() && // 字段必须是 pub
                    is_fuzzable_ty(field.ty(tcx, substs).peel_refs(), tcx)
                })
            } else if adt_def.is_enum() {
                adt_def.variants().iter().all(|variant| {
                    variant
                        .fields
                        .iter()
                        .all(|field| is_fuzzable_ty(field.ty(tcx, substs).peel_refs(), tcx))
                })
            } else {
                false // union 暂不处理
            }
        }

        // 其他类型默认不可 Fuzz
        _ => false,
    }
}

pub fn fn_sig_without_binders<'tcx>(fn_did: DefId, tcx: TyCtxt<'tcx>) -> FnSig<'tcx> {
    let early_fn_sig = tcx.fn_sig(fn_did);
    let binder_fn_sig = early_fn_sig.instantiate_identity();
    tcx.liberate_late_bound_regions(fn_did, binder_fn_sig)
}

pub fn fn_sig_with_generic_args<'tcx>(
    fn_did: DefId,
    args: &[ty::GenericArg<'tcx>],
    tcx: TyCtxt<'tcx>,
) -> FnSig<'tcx> {
    let early_fn_sig = tcx.fn_sig(fn_did);
    let binder_fn_sig = early_fn_sig.instantiate(tcx, args);
    tcx.liberate_late_bound_regions(fn_did, binder_fn_sig)
}

pub fn fn_requires_monomorphization<'tcx>(fn_did: DefId, tcx: TyCtxt<'_>) -> bool {
    tcx.generics_of(fn_did).requires_monomorphization(tcx)
}

pub fn is_ty_eq<'tcx>(ty1: Ty<'tcx>, ty2: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let ty1 = tcx.erase_and_anonymize_regions(ty1);
    let ty2 = tcx.erase_and_anonymize_regions(ty2);
    return ty1 == ty2;
}

pub fn ty_complexity<'tcx>(ty: Ty<'tcx>) -> usize {
    match ty.kind() {
        // Reference, Array, Slice
        TyKind::Ref(_, inner_ty, _) | TyKind::Array(inner_ty, _) | TyKind::Slice(inner_ty) => {
            ty_complexity(*inner_ty) + 1
        }

        // Tuple
        TyKind::Tuple(tys) => tys.iter().fold(0, |ans, ty| ans.max(ty_complexity(ty))) + 1,

        // ADT
        TyKind::Adt(_, args) => {
            args.iter().fold(0, |ans, arg| {
                if let Some(ty) = arg.as_type() {
                    ans.max(ty_complexity(ty))
                } else {
                    ans
                }
            }) + 1
        }

        // the depth of other primitive type default to 1
        _ => 1,
    }
}
